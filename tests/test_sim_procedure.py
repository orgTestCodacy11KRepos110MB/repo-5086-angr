import os
import angr
import claripy
from angr.codenode import BlockNode, HookNode, SyscallNode

BIN_PATH = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', '..', 'binaries')

def test_ret_float():
    p = angr.load_shellcode(b'X', arch='i386')

    class F1(angr.SimProcedure):
        def run(self):
            return 12.5

    p.hook(0x1000, F1(cc=p.factory.cc(func_ty=angr.sim_type.parse_file('float (x)();')[0]['x'])))
    p.hook(0x2000, F1(cc=p.factory.cc(func_ty=angr.sim_type.parse_file('double (x)();')[0]['x'])))

    s = p.factory.call_state(addr=0x1000, ret_addr=0)
    succ = s.step()
    assert len(succ.successors) == 1
    s2 = succ.flat_successors[0]
    assert not s2.regs.st0.symbolic
    assert s2.solver.eval(s2.regs.st0.get_bytes(4, 4).raw_to_fp()) == 12.5

    s = p.factory.call_state(addr=0x2000, ret_addr=0)
    succ = s.step()
    assert len(succ.successors) == 1
    s2 = succ.flat_successors[0]
    assert not s2.regs.st0.symbolic
    assert s2.solver.eval(s2.regs.st0.raw_to_fp()) == 12.5

def test_syscall_and_simprocedure():
    bin_path = os.path.join(BIN_PATH, 'tests', 'cgc', 'CADET_00002')
    proj = angr.Project(bin_path, auto_load_libs=False)
    cfg = proj.analyses.CFGFast(normalize=True)

    # check syscall
    node = cfg.get_any_node(proj.loader.kernel_object.mapped_base + 1)
    func = proj.kb.functions[node.addr]

    assert node.is_simprocedure
    assert node.is_syscall
    assert not node.to_codenode().is_hook
    assert not proj.is_hooked(node.addr)
    assert func.is_syscall
    assert func.is_simprocedure
    assert type(proj.factory.snippet(node.addr)) == SyscallNode

    # check normal functions
    node = cfg.get_any_node(0x80480a0)
    func = proj.kb.functions[node.addr]

    assert not node.is_simprocedure
    assert not node.is_syscall
    assert not proj.is_hooked(node.addr)
    assert not func.is_syscall
    assert not func.is_simprocedure
    assert type(proj.factory.snippet(node.addr)) == BlockNode

    # check hooked functions
    proj.hook(0x80480a0, angr.SIM_PROCEDURES['libc']['puts']())
    cfg = proj.analyses.CFGFast(normalize=True)# rebuild cfg to updated nodes
    node = cfg.get_any_node(0x80480a0)
    func = proj.kb.functions[node.addr]

    assert node.is_simprocedure
    assert not node.is_syscall
    assert proj.is_hooked(node.addr)
    assert not func.is_syscall
    assert func.is_simprocedure
    assert type(proj.factory.snippet(node.addr)) == HookNode


if __name__ == '__main__':
    test_ret_float()
    test_syscall_and_simprocedure()
