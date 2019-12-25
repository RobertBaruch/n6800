from enum import IntEnum
import importlib
from typing import List, Dict, Tuple, Optional

from formal.verification import FormalData, Verification

from nmigen import Signal, Value, Elaboratable, Module, Cat, Const, Mux
from nmigen import ClockDomain, ClockSignal
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Past, Cover, Assume
from nmigen.build import Platform
from nmigen.cli import main_parser, main_runner
from nmigen.back.pysim import Simulator, Delay


class Reg8(IntEnum):
    """Values for specifying an 8-bit register for things
    like sources and destinations. Can also specify the
    (H)igh or (L)ow 8 bits of a 16-bit signal."""
    NONE = 0
    A = 1
    B = 2
    XH = 3
    XL = 4
    SPH = 5
    SPL = 6
    PCH = 7
    PCL = 8
    TMP8 = 9
    TMP16H = 10
    TMP16L = 11
    DIN = 12
    DOUT = 13


class Reg16(IntEnum):
    """Values for specifying a 16-bit register for things
    like sources and destinations."""
    NONE = 0
    X = 1
    SP = 2
    PC = 3
    TMP16 = 4
    ADDR = 5


class Core(Elaboratable):
    """The core of the CPU. There is another layer which
    handles I/O for the actual pins."""

    reg8_map: Dict[IntEnum, Tuple[Signal, bool]]
    reg16_map: Dict[IntEnum, Tuple[Signal, bool]]

    def __init__(self, verification: Verification = None):
        self.Addr = Signal(16)
        self.Din = Signal(8)
        self.Dout = Signal(8)
        self.RW = Signal(reset=1)  # 1 = read, 0 = write

        # registers
        self.a = Signal(8, reset_less=True)
        self.b = Signal(8, reset_less=True)
        self.x = Signal(16, reset_less=True)
        self.sp = Signal(16, reset_less=True)
        self.pc = Signal(16, reset_less=True)
        self.instr = Signal(8, reset_less=True)
        self.tmp8 = Signal(8, reset_less=True)
        self.tmp16 = Signal(16, reset_less=True)

        # busses
        self.src8_1 = Signal(8)  # Input 1 of the ALU
        self.src8_2 = Signal(8)  # Input 2 of the ALU
        self.alu8 = Signal(8)   # Output from the ALU
        self.src16 = Signal(16)     # Input to 16-bit inc/dec
        self.incdec16 = Signal(16)  # Output from 16-bit inc/dec

        # selectors for busses
        self.src8_1_select = Signal(Reg8)
        self.src8_2_select = Signal(Reg8)
        self.alu8_write = Signal(len(Reg8.__members__))
        self.src16_select = Signal(Reg16)
        self.src16_write = Signal(len(Reg16.__members__))
        self.incdec16_write = Signal(len(Reg16.__members__))

        # mappings of selectors to signals. The second tuple element is
        # whether the register is read/write.
        self.reg8_map = {
            Reg8.A: (self.a, True),
            Reg8.B: (self.b, True),
            Reg8.XH: (self.x[8:], True),
            Reg8.XL: (self.x[:8], True),
            Reg8.SPH: (self.sp[8:], True),
            Reg8.SPL: (self.sp[:8], True),
            Reg8.PCH: (self.pc[8:], True),
            Reg8.PCL: (self.pc[:8], True),
            Reg8.TMP8: (self.tmp8, True),
            Reg8.TMP16H: (self.tmp16[8:], True),
            Reg8.TMP16L: (self.tmp16[:8], True),
            Reg8.DIN: (self.Din, False),  # read-only register
            Reg8.DOUT: (self.Dout, True),
        }
        self.reg16_map = {
            Reg16.X: (self.x, True),
            Reg16.SP: (self.sp, True),
            Reg16.PC: (self.pc, True),
            Reg16.TMP16: (self.tmp16, True),
            Reg16.ADDR: (self.Addr, True),
        }

        # internal state
        self.reset_state = Signal(2)  # where we are during reset
        self.cycle = Signal(4)        # where we are during instr processing

        self.end_instr_flag = Signal()    # performs end-of-instruction actions
        self.end_instr_addr = Signal(16)  # where the next instruction is

        # Formal verification
        self.verification = verification
        self.formalData = FormalData(verification)

    def ports(self) -> List[Signal]:
        return [self.Addr, self.Din, self.Dout, self.RW]

    def elaborate(self, platform: Platform) -> Module:
        m = Module()

        m.d.comb += self.end_instr_flag.eq(0)

        self.src_bus_setup(m, self.reg8_map, self.src8_1, self.src8_1_select)
        self.src_bus_setup(m, self.reg8_map, self.src8_2, self.src8_2_select)
        self.dest_bus_setup(m, self.reg8_map, self.alu8, self.alu8_write)
        self.src_bus_setup(m, self.reg16_map, self.src16, self.src16_select)
        self.dest_bus_setup(m, self.reg16_map, self.src16, self.src16_write)
        self.dest_bus_setup(m, self.reg16_map,
                            self.incdec16, self.incdec16_write)

        self.reset_handler(m)
        self.end_instr_flag_handler(m)
        with m.If(self.reset_state == 3):
            with m.If(self.cycle == 0):
                self.fetch(m)
            with m.Else():
                self.execute(m)
        self.maybe_do_formal_verification(m)

        return m

    def src_bus_setup(self, m: Module, reg_map: Dict[IntEnum, Tuple[Signal, bool]], bus: Signal, selector: Signal):
        with m.Switch(selector):
            for e, reg in reg_map.items():
                with m.Case(e):
                    m.d.comb += bus.eq(reg[0])
            with m.Default():
                m.d.comb += bus.eq(0)

    def dest_bus_setup(self, m: Module, reg_map: Dict[IntEnum, Tuple[Signal, bool]], bus: Signal, bitmap: Signal):
        for e, reg in reg_map.items():
            if reg[1]:
                with m.If(bitmap[e.value]):
                    m.d.ph1 += reg[0].eq(bus)

    def reset_handler(self, m: Module):
        """Generates logic for reading the reset vector at 0xFFFE
        and jumping there."""
        with m.Switch(self.reset_state):
            with m.Case(0):
                m.d.ph1 += self.Addr.eq(0xFFFE)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.reset_state.eq(1)
            with m.Case(1):
                m.d.ph1 += self.Addr.eq(0xFFFF)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.tmp8.eq(self.Din)
                m.d.ph1 += self.reset_state.eq(2)
            with m.Case(2):
                m.d.ph1 += self.reset_state.eq(3)
                reset_vec = Cat(self.Din, self.tmp8)
                self.end_instr(m, reset_vec)

    def end_instr_flag_handler(self, m: Module):
        """Generates logic for handling the end of an instruction."""
        with m.If(self.end_instr_flag):
            m.d.ph1 += self.pc.eq(self.end_instr_addr)
            m.d.ph1 += self.Addr.eq(self.end_instr_addr)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.cycle.eq(0)

    def fetch(self, m: Module):
        """Fetch the opcode at PC, which should already be on the address lines.
        The opcode is on the data lines by the end of the cycle.
        We always increment PC and Addr and go to instruction cycle 1."""
        m.d.ph1 += self.instr.eq(self.Din)
        m.d.ph1 += self.cycle.eq(1)
        m.d.ph1 += self.RW.eq(1)
        m.d.ph1 += self.pc.eq(self.pc + 1)
        m.d.ph1 += self.Addr.eq(self.pc + 1)

    def maybe_do_formal_verification(self, m: Module):
        """If formal verification is enabled, take pre- and post-snapshots, and do asserts.

        A pre-snapshot is taken of the registers when self.Din is the instruction we're
        looking for, and we're on cycle 0. We use Din because Din -> instr only at the
        *end* of cycle 0.

        A post-snapshot is taken of the registers during cycle 0 of the *next* instruction.
        It's not really a "snapshot", in that the CPU state aren't stored. All verification
        takes place using combinatorial statements.
        """
        if self.verification is not None:
            with m.If((self.cycle == 0) & (self.reset_state == 3)):
                with m.If(self.verification.valid(self.Din)):
                    self.formalData.preSnapshot(
                        m, self.Din, self.a, self.b, self.x, self.sp, self.pc)
                with m.Else():
                    self.formalData.noSnapshot(m)

                with m.If(self.formalData.snapshot_taken):
                    self.formalData.postSnapshot(
                        m, self.a, self.b, self.x, self.sp, self.pc)
                    self.verification.check(m, self.instr, self.formalData)

    def execute(self, m: Module):
        """Execute the instruction in the instr register."""
        with m.Switch(self.instr):
            with m.Case("00000001"):  # NOP
                self.NOP(m)
            with m.Case("01111110"):  # JMP ext
                self.JMPext(m)
            with m.Default():  # Illegal
                self.end_instr(m, self.pc)

    def NOP(self, m: Module):
        self.end_instr(m, self.pc)

    def JMPext(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.cycle.eq(2)
            if self.verification is not None:
                self.formalData.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 2):
            new_pc = Cat(self.Din, self.tmp16[8:])
            self.end_instr(m, new_pc)
            if self.verification is not None:
                self.formalData.read(m, self.Addr, self.Din)

    def end_instr(self, m: Module, addr: Statement):
        m.d.comb += self.end_instr_addr.eq(addr)
        m.d.comb += self.end_instr_flag.eq(1)


if __name__ == "__main__":
    parser = main_parser()
    parser.add_argument("--insn")
    args = parser.parse_args()

    verification: Optional[Verification] = None
    if args.insn is not None:
        module = importlib.import_module(f"formal.formal_{args.insn}")
        formal_class = getattr(module, "Formal")
        verification = formal_class()

    m = Module()
    m.submodules.core = core = Core(verification)
    m.domains.ph1 = ph1 = ClockDomain("ph1")

    rst = Signal()
    ph1clk = ClockSignal("ph1")
    ph1.rst = rst

    if verification is not None:
        # Cycle counter
        cycle2 = Signal(6, reset_less=True)
        m.d.ph1 += cycle2.eq(cycle2 + 1)

        # Force a reset
        # m.d.comb += Assume(rst == (cycle2 < 8))

        with m.If(cycle2 == 20):
            m.d.ph1 += Cover(verification.valid(core.instr))
            m.d.ph1 += Assume(verification.valid(core.instr))

        # Verify reset does what it's supposed to
        with m.If(Past(rst, 4) & ~Past(rst, 3) & ~Past(rst, 2) & ~Past(rst)):
            m.d.ph1 += Assert(Past(core.Addr, 2) == 0xFFFE)
            m.d.ph1 += Assert(Past(core.Addr) == 0xFFFF)
            m.d.ph1 += Assert(core.Addr[8:] == Past(core.Din, 2))
            m.d.ph1 += Assert(core.Addr[:8] == Past(core.Din))
            m.d.ph1 += Assert(core.Addr == core.pc)

        main_runner(parser, args, m, ports=core.ports() + [ph1clk, rst])

    else:
        # Fake memory
        mem = {
            0xFFFE: 0x12,
            0xFFFF: 0x34,
            0x1234: 0x7E,  # JMP 0xA010
            0x1235: 0xA0,
            0x1236: 0x10,
            0xA010: 0x01,  # NOP
        }
        with m.Switch(core.Addr):
            for addr, data in mem.items():
                with m.Case(addr):
                    m.d.comb += core.Din.eq(data)
            with m.Default():
                m.d.comb += core.Din.eq(0xFF)

        sim = Simulator(m)
        sim.add_clock(1e-6, domain="ph1")

        def process():
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield

        sim.add_sync_process(process, domain="ph1")
        with sim.write_vcd("test.vcd", "test.gtkw", traces=core.ports()):
            sim.run()
