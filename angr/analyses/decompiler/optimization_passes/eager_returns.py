from typing import Any, Tuple, Dict, List
from itertools import count
import copy
import logging
import inspect

import networkx

import ailment
from ailment.statement import Jump
from ailment.expression import Const
from .. import RegionIdentifier

from ..condition_processor import ConditionProcessor, EmptyBlockNotice
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..structuring import RecursiveStructurer, PhoenixStructurer

_l = logging.getLogger(name=__name__)


class EagerReturnsSimplifier(OptimizationPass):
    """
    Some compilers (if not all) generate only one returning block for a function regardless of how many returns there
    are in the source code. This oftentimes result in irreducible graphs and reduce the readability of the decompiled
    code. This optimization pass will make the function return eagerly by duplicating the return site of a function
    multiple times and assigning one copy of the return site to each of its sources when certain thresholds are met.

    Note that this simplifier may reduce the readability of the generated code in certain cases, especially if the graph
    is already reducible without applying this simplifier.

    :ivar int max_level:    Number of times that we repeat the process of making returns eager.
    :ivar int min_indegree: The minimum in-degree of the return site to be duplicated.
    :ivar node_idx:         The next node index. Each duplicated return site gets assigned a unique index, otherwise
                            those duplicates will be considered as the same block in the graph because they have the
                            same hash.
    """

    # TODO: This optimization pass may support more architectures and platforms
    ARCHES = [
        "X86",
        "AMD64",
        "ARMCortexM",
        "ARMHF",
        "ARMEL",
    ]
    PLATFORMS = ["cgc", "linux"]
    STAGE = OptimizationPassStage.BEFORE_REGION_IDENTIFICATION
    NAME = "Duplicate return blocks to reduce goto statements"
    DESCRIPTION = inspect.cleandoc(__doc__[: __doc__.index(":ivar")])  # pylint:disable=unsubscriptable-object

    def __init__(
        self,
        func,
        blocks_by_addr=None,
        blocks_by_addr_and_idx=None,
        graph=None,
        # internal parameters that should be used by Clinic
        node_idx_start=0,
        # settings
        max_level=2,
        min_indegree=2,
        reaching_definitions=None,
        region_identifier=None,
        **kwargs,
    ):

        super().__init__(
            func, blocks_by_addr=blocks_by_addr, blocks_by_addr_and_idx=blocks_by_addr_and_idx, graph=graph, **kwargs
        )

        self.max_level = max_level
        self.min_indegree = min_indegree
        self.node_idx = count(start=node_idx_start)
        self._rd = reaching_definitions
        self.ri = region_identifier

        self.goto_locations = None
        self.func_name = self._func.name
        self.binary_name = self.project.loader.main_object.binary_basename
        self.target_name = f"{self.binary_name}.{self.func_name}"
        self.graph_copy = None
        self.analyze()

    def _check(self):

        # does this function have end points?
        if not self._func.endpoints:
            return False, None

        # TODO: More filtering

        return True, None

    def _analyze(self, cache=None):

        # for each block with no successors and more than 1 predecessors, make copies of this block and link it back to
        # the sources of incoming edges
        self.graph_copy = networkx.DiGraph(self._graph)
        self.last_graph = None
        graph_updated = False

        # attempt at most N levels
        for _ in range(self.max_level):
            success, graph_has_gotos = self._structure_graph()
            if not success:
                self.graph_copy = self.last_graph
                break

            if not graph_has_gotos:
                _l.debug("Graph has no gotos. Leaving analysis...")
                break

            # make a clone of graph copy to recover in the event of failure
            self.last_graph = self.graph_copy.copy()
            r = self._analyze_core(self.graph_copy)
            if not r:
                break
            graph_updated = True

        # the output graph
        if graph_updated and self.graph_copy is not None:
            self.out_graph = self.graph_copy

    #
    # taken from deduplicator
    #

    def _structure_graph(self):
        # reset gotos
        self.kb.gotos.locations[self._func.addr] = set()

        # do structuring
        self.ri = self.project.analyses[RegionIdentifier].prep(kb=self.kb)(
            self._func, graph=self.graph_copy, cond_proc=self.ri.cond_proc, force_loop_single_exit=False,
        )
        rs = self.project.analyses[RecursiveStructurer].prep(kb=self.kb)(
            copy.deepcopy(self.ri.region),
            cond_proc=self.ri.cond_proc,
            func=self._func,
            structurer_cls=PhoenixStructurer
        )
        if not rs.result.nodes:
            _l.critical(f"Failed to redo structuring on {self.target_name}")
            return False, False

        self.project.analyses.RegionSimplifier(self._func, rs.result, kb=self.kb, variable_kb=self._variable_kb)

        # collect gotos
        self.goto_locations = {goto.addr for goto in self.kb.gotos.locations[self._func.addr]}
        return True, len(self.goto_locations) != 0

    def _block_has_goto_edge(self, block: ailment.Block):
        if block.addr in self.goto_locations or \
                any(stmt.tags['ins_addr'] in self.goto_locations for stmt in block.statements):
            return True


    def _analyze_core(self, graph: networkx.DiGraph):

        endnodes = [node for node in graph.nodes() if graph.out_degree[node] == 0]
        graph_changed = False

        # to_update is keyed by the region head.
        # this is because different end nodes may lead to the same region head: consider the case of the typical "fork"
        # region where stack canary is checked in x86-64 binaries.
        to_update: Dict[Any, Tuple[List[Tuple[Any, Any]], networkx.DiGraph]] = {}

        for end_node in endnodes:
            in_edges = list(graph.in_edges(end_node))

            if len(in_edges) > 1:
                region = networkx.DiGraph()
                region.add_node(end_node)
                region_head = end_node
            elif len(in_edges) == 1:
                # back-trace until it reaches a node with two predecessors
                region, region_head = self._single_entry_region(graph, end_node)
                tmp_in_edges = graph.in_edges(region_head)
                # remove in_edges that are coming from a node inside the region
                in_edges = []
                for src, dst in tmp_in_edges:
                    if src not in region:
                        in_edges.append((src, dst))
            else:  # len(in_edges) == 0
                continue

            # region and in_edge might have been updated. re-check
            if not in_edges:
                # this is a single connected component in the graph
                # no need to duplicate anything
                continue
            if len(in_edges) == 1:
                # there is no need to duplicate it
                continue
            if len(in_edges) < self.min_indegree:
                # does not meet the threshold
                continue

            to_update[region_head] = in_edges, region

        for region_head, (in_edges, region) in to_update.items():
            # update the graph
            removed_edges = list()
            for in_edge in in_edges:
                pred_node = in_edge[0]
                if not self._block_has_goto_edge(pred_node):
                    continue

                removed_edges.append(in_edge)

                # Modify the graph and then add an edge to the copy of the region
                copies = {}
                queue = [(pred_node, region_head)]
                while queue:
                    pred, node = queue.pop(0)
                    if node in copies:
                        node_copy = copies[node]
                    else:
                        node_copy = copy.deepcopy(node)
                        node_copy.idx = next(self.node_idx)
                        copies[node] = node_copy

                    # modify Jump.target_idx accordingly
                    graph.add_edge(pred, node_copy)
                    try:
                        last_stmt = ConditionProcessor.get_last_statement(pred)
                        if isinstance(last_stmt, Jump) and isinstance(last_stmt.target, Const):
                            if last_stmt.target.value == node_copy.addr:
                                last_stmt.target_idx = node_copy.idx
                    except EmptyBlockNotice:
                        pass

                    for succ in region.successors(node):
                        queue.append((node_copy, succ))

            if not removed_edges:
                continue

            # remove all in-edges
            graph.remove_edges_from(removed_edges)
            # remove the node to be copied
            graph.remove_nodes_from(region)
            graph_changed = True

        return graph_changed

    @staticmethod
    def _single_entry_region(graph, end_node) -> Tuple[networkx.DiGraph, Any]:
        """
        Back track on the graph from `end_node` and find the longest chain of nodes where each node has only one
        predecessor and one successor (the second-to-last node may have two successors to account for the typical
        stack-canary-detection logic).

        :param end_node:    A node in the graph.
        :return:            A graph of nodes where the first node either has no predecessors or at least two
                            predecessors.
        """

        def _is_fork_node(node_) -> bool:
            """
            Check if the node and its successors form a "fork" region. A "fork" region is a region where:
            - The entry node has two successors,
            - Each successor has only the entry node as its predecessor.
            - Each successor has no successors.
            """

            succs = list(graph.successors(node_))
            if len(succs) != 2:
                return False
            for succ in succs:
                if graph.in_degree[succ] != 1:
                    return False
                if graph.out_degree[succ] != 0:
                    return False
            return True

        region = networkx.DiGraph()
        region.add_node(end_node)

        traversed = {end_node}
        region_head = end_node
        while True:
            preds = list(graph.predecessors(region_head))
            if len(preds) != 1:
                break
            second_to_last_node = region_head is end_node

            pred_node = preds[0]

            if pred_node in traversed:
                break

            if second_to_last_node:
                if _is_fork_node(pred_node):
                    # add the entire "fork" to the region
                    for succ in graph.successors(pred_node):
                        region.add_edge(pred_node, succ)
                elif graph.out_degree[pred_node] != 1:
                    # the predecessor has more than one successor, and it's not a fork node
                    break

                if graph.in_degree[pred_node] == 1:
                    # continue search
                    pass
                else:
                    region.add_edge(pred_node, region_head)
                    traversed.add(pred_node)
                    region_head = pred_node
                    break
            elif not second_to_last_node and graph.out_degree[pred_node] != 1:
                break

            region.add_edge(pred_node, region_head)
            traversed.add(pred_node)
            region_head = pred_node

        return region, region_head
