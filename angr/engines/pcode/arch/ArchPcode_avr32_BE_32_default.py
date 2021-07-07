###
### This file was automatically generated
###

from archinfo.arch import register_arch, Endness, Register

from .common import ArchPcode


class ArchPcode_avr32_BE_32_default(ArchPcode):
    name = 'avr32:BE:32:default'
    pcode_arch = 'avr32:BE:32:default'
    description = 'Generic AVR32-A big-endian'
    bits = 32
    ip_offset = 0x103c
    sp_offset = 0x1034
    bp_offset = sp_offset
    instruction_endness = Endness.BE
    register_list = [
        Register('sr', 4, 0x0),
        Register('evba', 4, 0x4),
        Register('acba', 4, 0x8),
        Register('cpucr', 4, 0xc),
        Register('ecr', 4, 0x10),
        Register('rsr_sup', 4, 0x14),
        Register('rsr_int0', 4, 0x18),
        Register('rsr_int1', 4, 0x1c),
        Register('rsr_int2', 4, 0x20),
        Register('rsr_int3', 4, 0x24),
        Register('rsr_ex', 4, 0x28),
        Register('rsr_nmi', 4, 0x2c),
        Register('rsr_dbg', 4, 0x30),
        Register('rar_sup', 4, 0x34),
        Register('rar_int0', 4, 0x38),
        Register('rar_int1', 4, 0x3c),
        Register('rar_int2', 4, 0x40),
        Register('rar_int3', 4, 0x44),
        Register('rar_ex', 4, 0x48),
        Register('rar_nmi', 4, 0x4c),
        Register('rar_dbg', 4, 0x50),
        Register('jecr', 4, 0x54),
        Register('josp', 4, 0x58),
        Register('java_lv0', 4, 0x5c),
        Register('java_lv1', 4, 0x60),
        Register('java_lv2', 4, 0x64),
        Register('java_lv3', 4, 0x68),
        Register('java_lv4', 4, 0x6c),
        Register('java_lv5', 4, 0x70),
        Register('java_lv6', 4, 0x74),
        Register('java_lv7', 4, 0x78),
        Register('jtba', 4, 0x7c),
        Register('jbcr', 4, 0x80),
        Register('config0', 4, 0x100),
        Register('config1', 4, 0x104),
        Register('count', 4, 0x108),
        Register('compare', 4, 0x10c),
        Register('tlbehi', 4, 0x110),
        Register('tlbelo', 4, 0x114),
        Register('ptbr', 4, 0x118),
        Register('tlbear', 4, 0x11c),
        Register('mmucr', 4, 0x120),
        Register('tlbarlo', 4, 0x124),
        Register('tlbarhi', 4, 0x128),
        Register('pccnt', 4, 0x12c),
        Register('pcnt0', 4, 0x130),
        Register('pcnt1', 4, 0x134),
        Register('pccr', 4, 0x138),
        Register('bear', 4, 0x13c),
        Register('mpuar0', 4, 0x140),
        Register('mpuar1', 4, 0x144),
        Register('mpuar2', 4, 0x148),
        Register('mpuar3', 4, 0x14c),
        Register('mpuar4', 4, 0x150),
        Register('mpuar5', 4, 0x154),
        Register('mpuar6', 4, 0x158),
        Register('mpuar7', 4, 0x15c),
        Register('mpupsr0', 4, 0x160),
        Register('mpupsr1', 4, 0x164),
        Register('mpupsr2', 4, 0x168),
        Register('mpupsr3', 4, 0x16c),
        Register('mpupsr4', 4, 0x170),
        Register('mpupsr5', 4, 0x174),
        Register('mpupsr6', 4, 0x178),
        Register('mpupsr7', 4, 0x17c),
        Register('mpucra', 4, 0x180),
        Register('mpucrb', 4, 0x184),
        Register('mpubra', 4, 0x188),
        Register('mpubrb', 4, 0x18c),
        Register('mpuapra', 4, 0x190),
        Register('mpuaprb', 4, 0x194),
        Register('mpucr', 4, 0x198),
        Register('ss_status', 4, 0x19c),
        Register('ss_adrf', 4, 0x1a0),
        Register('ss_adrr', 4, 0x1a4),
        Register('ss_adr0', 4, 0x1a8),
        Register('ss_adr1', 4, 0x1ac),
        Register('ss_sp_sys', 4, 0x1b0),
        Register('ss_sp_app', 4, 0x1b4),
        Register('ss_rar', 4, 0x1b8),
        Register('ss_rsr', 4, 0x1bc),
        Register('r0', 4, 0x1000),
        Register('r1', 4, 0x1004),
        Register('r2', 4, 0x1008),
        Register('r3', 4, 0x100c),
        Register('r4', 4, 0x1010),
        Register('r5', 4, 0x1014),
        Register('r6', 4, 0x1018),
        Register('r7', 4, 0x101c),
        Register('r8', 4, 0x1020),
        Register('r9', 4, 0x1024),
        Register('r10', 4, 0x1028),
        Register('r11', 4, 0x102c),
        Register('r12', 4, 0x1030),
        Register('sp', 4, 0x1034),
        Register('lr', 4, 0x1038),
        Register('pc', 4, 0x103c, alias_names=('ip',)),
        Register('c', 1, 0x1100),
        Register('z', 1, 0x1101),
        Register('n', 1, 0x1102),
        Register('v', 1, 0x1103),
        Register('q', 1, 0x1104),
        Register('l', 1, 0x1105),
        Register('t', 1, 0x110e),
        Register('r', 1, 0x110f),
        Register('gm', 1, 0x1110),
        Register('i0m', 1, 0x1111),
        Register('i1m', 1, 0x1112),
        Register('i2m', 1, 0x1113),
        Register('i3m', 1, 0x1114),
        Register('em', 1, 0x1115),
        Register('m0', 1, 0x1116),
        Register('m1', 1, 0x1117),
        Register('m2', 1, 0x1118),
        Register('d', 1, 0x111a),
        Register('dm', 1, 0x111b),
        Register('j', 1, 0x111c),
        Register('h', 1, 0x111d),
        Register('always_true', 1, 0x1120),
        Register('stadd', 4, 0x1200),
        Register('ldadd', 4, 0x1204),
        Register('contextreg', 4, 0x1300)
    ]

register_arch(['avr32:be:32:default'], 32, Endness.BE, ArchPcode_avr32_BE_32_default)