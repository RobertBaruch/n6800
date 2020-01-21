# core.py: Core code for the 6800 CPU
# Copyright (C) 2020 Robert Baruch <robert.c.baruch@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

# Generate and verify code:
# python3 core.py --insn jmp generate -t il > core.il
# sby -f core.sby

# Simulate code:
# python3 core.py
# gtkwave test.gtkw

from enum import IntEnum
import importlib
from typing import List, Dict, Tuple, Optional

from formal.verification import FormalData, Verification
from alu8 import ALU8Func, ALU8, LCat
from consts.consts import ModeBits, Flags

from nmigen import Signal, Value, Elaboratable, Module, Cat, Const, Mux, signed, Repl
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

    def __init__(self, verification: Verification = None):
        # outputs
        self.Addr = Signal(16)
        self.Dout = Signal(8)
        self.RW = Signal(reset=1)  # 1 = read, 0 = write
        self.VMA = Signal()  # 1 = address is valid
        self.BA = Signal()  # 1 = bus available (makes Addr, Data, RW go tristate)

        # inputs
        self.Din = Signal(8)
        self.IRQ = Signal()
        self.NMI = Signal()

        # registers
        self.a = Signal(8, reset_less=True)
        self.b = Signal(8, reset_less=True)
        self.x = Signal(16, reset_less=True)
        self.sp = Signal(16, reset_less=True)
        self.pc = Signal(16, reset_less=True)
        self.instr = Signal(8, reset_less=True)
        self.tmp16 = Signal(16, reset_less=True)

        # busses
        self.src8_1 = Signal(8)  # Input 1 of the ALU
        self.src8_2 = Signal(8)  # Input 2 of the ALU
        self.alu8 = Signal(8)  # Output from the ALU
        self.ccs = Signal(8)  # Flags from the ALU

        # function control
        self.alu8_func = Signal(ALU8Func)

        # internal state
        self.reset_state = Signal(2)  # where we are during reset
        self.interrupt = Signal()  # whether we're handling an interrupt
        self.interrupt_vec = Signal(2)  # which interrupt vector to use:
        # 0 = IRQ
        # 1 = SWI
        # 2 = NMI
        # 3 = Reset
        self.cycle = Signal(4)  # where we are during an instruction
        self.mode = Signal(2)  # mode bits, decoded by ModeBits
        self.wai = Signal()  # if waiting for interrupt

        self.end_instr_flag = Signal()  # performs end-of-instruction actions
        self.end_instr_addr = Signal(16)  # where the next instruction is

        # Formal verification
        self.verification = verification
        self.formalData = FormalData(verification)

    def ports(self) -> List[Signal]:
        return [
            self.Addr,
            self.Din,
            self.Dout,
            self.RW,
            self.VMA,
            self.BA,
            self.IRQ,
            self.NMI,
        ]

    def elaborate(self, platform: Platform) -> Module:
        m = Module()
        m.submodules.alu = alu = ALU8()

        # defaults
        m.d.comb += self.end_instr_flag.eq(0)
        m.d.comb += self.alu8_func.eq(ALU8Func.NONE)
        m.d.comb += self.wai.eq(0)
        m.d.ph1 += self.VMA.eq(1)
        m.d.ph1 += self.BA.eq(0)
        m.d.ph1 += self.cycle.eq(self.cycle + 1)

        # some common instruction decoding
        m.d.comb += self.mode.eq(self.instr[4:6])

        m.d.comb += alu.input1.eq(self.src8_1)
        m.d.comb += alu.input2.eq(self.src8_2)
        m.d.comb += self.alu8.eq(alu.output)
        m.d.comb += alu.func.eq(self.alu8_func)
        m.d.comb += self.ccs.eq(alu.ccs)

        self.reset_handler(m)
        with m.If(self.reset_state == 3):
            with m.If(self.interrupt == 1):
                self.interrupt_handler(m)
            with m.Elif(self.cycle == 0):
                self.fetch(m)
            with m.Else():
                self.execute(m)
        self.maybe_do_formal_verification(m)
        self.end_instr_flag_handler(m)

        return m

    def reset_handler(self, m: Module):
        """Generates logic for reading the reset vector at 0xFFFE
        and jumping there."""
        with m.Switch(self.reset_state):
            with m.Case(0):
                m.d.ph1 += self.Addr.eq(0xFFFE)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.reset_state.eq(1)
            with m.Case(1):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.tmp16[8:].eq(self.Din)
                m.d.ph1 += self.reset_state.eq(2)
            with m.Case(2):
                m.d.ph1 += self.reset_state.eq(3)
                reset_vec = LCat(self.tmp16[8:], self.Din)
                self.end_instr(m, reset_vec)

    def end_instr_flag_handler(self, m: Module):
        """Generates logic for what additional actions to do the end of an instruction."""
        with m.If(self.end_instr_flag):

            with m.If(~self.wai):
                m.d.ph1 += self.pc.eq(self.end_instr_addr)
                m.d.ph1 += self.cycle.eq(0)
                with m.If(self.NMI):
                    m.d.ph1 += self.interrupt.eq(1)
                    m.d.ph1 += self.interrupt_vec.eq(2)
                    m.d.ph1 += self.Addr.eq(self.sp)
                    m.d.ph1 += self.RW.eq(0)
                    m.d.ph1 += self.Dout.eq(self.end_instr_addr[:8])
                with m.Elif(self.IRQ & ~self.ccs[Flags.I]):
                    m.d.ph1 += self.interrupt.eq(1)
                    m.d.ph1 += self.interrupt_vec.eq(0)
                    m.d.ph1 += self.Addr.eq(self.sp)
                    m.d.ph1 += self.RW.eq(0)
                    m.d.ph1 += self.Dout.eq(self.end_instr_addr[:8])
                with m.Else():
                    m.d.ph1 += self.interrupt.eq(0)
                    m.d.ph1 += self.Addr.eq(self.end_instr_addr)
                    m.d.ph1 += self.RW.eq(1)

            with m.Else():
                m.d.ph1 += self.cycle.eq(self.cycle)
                with m.If(self.NMI):
                    m.d.ph1 += self.interrupt.eq(1)
                    m.d.comb += self.alu8_func.eq(ALU8Func.SEI)
                    m.d.ph1 += self.Addr.eq(0xFFFC)
                    m.d.ph1 += self.VMA.eq(1)
                    m.d.ph1 += self.RW.eq(1)
                    m.d.ph1 += self.cycle.eq(8)
                with m.Elif(self.IRQ & ~self.ccs[Flags.I]):
                    m.d.ph1 += self.interrupt.eq(1)
                    m.d.comb += self.alu8_func.eq(ALU8Func.SEI)
                    m.d.ph1 += self.Addr.eq(0xFFF8)
                    m.d.ph1 += self.VMA.eq(1)
                    m.d.ph1 += self.RW.eq(1)
                    m.d.ph1 += self.cycle.eq(8)
                with m.Else():
                    m.d.ph1 += self.VMA.eq(0)
                    m.d.ph1 += self.BA.eq(1)

    def interrupt_handler(self, m: Module):
        with m.Switch(self.cycle):
            with m.Case(0):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.pc[8:])

            with m.Case(1):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.x[:8])

            with m.Case(2):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.x[8:])

            with m.Case(3):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.a)

            with m.Case(4):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.b)

            with m.Case(5):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.ccs)

            with m.Case(6):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.Case(7):
                m.d.ph1 += self.sp.eq(self.Addr)
                m.d.comb += self.alu8_func.eq(ALU8Func.SEI)
                m.d.ph1 += self.Addr.eq(0xFFF8 | (self.interrupt_vec << 1))
                m.d.ph1 += self.VMA.eq(1)
                m.d.ph1 += self.RW.eq(1)

            with m.Case(8):
                m.d.ph1 += self.tmp16[8:].eq(self.Din)
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.ph1 += self.VMA.eq(1)
                m.d.ph1 += self.RW.eq(1)

            with m.Case(9):
                m.d.ph1 += self.interrupt.eq(0)
                self.end_instr(m, LCat(self.tmp16[8:], self.Din))

    def fetch(self, m: Module):
        """Fetch the opcode at PC, which should already be on the address lines.
        The opcode is on the data lines by the end of the cycle.
        We always increment PC and Addr and go to instruction cycle 1."""
        m.d.ph1 += self.instr.eq(self.Din)
        m.d.ph1 += self.RW.eq(1)
        m.d.ph1 += self.pc.eq(self.pc + 1)
        m.d.ph1 += self.Addr.eq(self.Addr + 1)

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

                with m.If(self.verification.valid(self.Din) & (~self.interrupt)):
                    m.d.ph1 += self.formalData.preSnapshot(
                        m, self.Din, self.ccs, self.a, self.b, self.x, self.sp, self.pc
                    )
                with m.Else():
                    m.d.ph1 += self.formalData.noSnapshot(m)

                with m.If(self.formalData.snapshot_taken):
                    m.d.comb += self.formalData.postSnapshot(
                        m, self.ccs, self.a, self.b, self.x, self.sp, self.pc
                    )
                    self.verification.verify(m, self.instr, self.formalData)

            with m.Elif(Past(self.wai) & self.formalData.snapshot_taken):
                m.d.comb += self.formalData.postSnapshot(
                    m, self.ccs, self.a, self.b, self.x, self.sp, self.pc
                )
                self.verification.verify(m, self.instr, self.formalData)
                m.d.ph1 += self.formalData.noSnapshot(m)

            with m.Elif(self.formalData.snapshot_taken):
                m.d.ph1 += self.formalData.snapshot_signals(
                    m,
                    addr=self.Addr,
                    din=self.Din,
                    dout=self.Dout,
                    rw=self.RW,
                    vma=self.VMA,
                    ba=self.BA,
                    irq=self.IRQ,
                    nmi=self.NMI,
                )

    def execute(self, m: Module):
        """Executes the instruction in the instr register.
        """
        with m.Switch(self.instr):
            with m.Case("00000001"):  # NOP
                self.NOP(m)
            with m.Case("00000110"):  # TAP
                self.TAP(m)
            with m.Case("00000111"):  # TPA
                self.TPA(m)
            with m.Case("0000100-"):  # INX/DEX
                self.IN_DE_X(m)
            with m.Case("0000101-"):  # CLV, SEV
                self.CL_SE_V(m)
            with m.Case("0000110-"):  # CLC, SEC
                self.CL_SE_C(m)
            with m.Case("0000111-"):  # CLI, SEI
                self.CL_SE_I(m)
            with m.Case("0001000-"):  # SBA, CBA
                self.SBA_CBA(m)
            with m.Case("0001001-"):  # TAB, TBA
                self.TAB_TBA(m)
            with m.Case("00011011"):  # ABA
                self.ABA(m)
            with m.Case("00011001"):  # DAA
                self.DAA(m)
            with m.Case("0010----"):  # Branch instructions
                self.BR(m)
            with m.Case("00110000", "00110101"):  # TSX, TXS
                self.TSX_TXS(m)
            with m.Case("00110001", "00110100"):  # INS, DES
                self.INS_DES(m)
            with m.Case("0011001-"):  # PUL A, PUL B
                self.PUL2(m)
            with m.Case("0011011-"):  # PSH A, PSH B
                self.PSH(m)
            with m.Case("00111001"):  # RTS
                self.RTS(m)
            with m.Case("00111011"):  # RTI
                self.RTI(m)
            with m.Case("00111110"):  # WAI
                self.WAI(m)
            with m.Case("00111111"):  # SWI
                self.SWI(m)

            with m.Case("01--0000"):  # NEG
                self.ALU2(m, ALU8Func.SUB, 0, 1)
            with m.Case("01--0011"):  # COM
                self.ALU2(m, ALU8Func.COM, 0, 1)
            with m.Case("01--0100"):  # LSR
                self.ALU2(m, ALU8Func.LSR, 0, 1)
            with m.Case("01--0110"):  # ROR
                self.ALU2(m, ALU8Func.ROR, 0, 1)
            with m.Case("01--0111"):  # ASR
                self.ALU2(m, ALU8Func.ASR, 0, 1)
            with m.Case("01--1000"):  # ASL
                self.ALU2(m, ALU8Func.ASL, 0, 1)
            with m.Case("01--1001"):  # ROL
                self.ALU2(m, ALU8Func.ROL, 0, 1)
            with m.Case("01--1010"):  # DEC
                self.ALU2(m, ALU8Func.DEC, 0, 1)
            with m.Case("01--1100"):  # INC
                self.ALU2(m, ALU8Func.INC, 0, 1)
            with m.Case("01--1101"):  # TST
                self.ALU2(m, ALU8Func.SUB, 1, 0, store=False)
            with m.Case("01--1111"):  # CLR
                self.ALU2(m, ALU8Func.SUB, 1, 1)

            with m.Case("011-1110"):  # JMP
                self.JMP(m)
            with m.Case("10--1100"):  # CPX
                self.CPX(m) # 120 LUTS
            with m.Case("10001101"):  # BSR
                self.JSR_BSR(m) # 130 LUTS
            with m.Case("1---1110"):  # LDS, LDX
                self.LDS_LDX(m) # 120 LUTS
            with m.Case("1-011111", "1-1-1111"):  # STS, STX
                self.STS_STX(m)

            with m.Case("1---0110"):  # LDA
                self.ALU(m, ALU8Func.LD)
            with m.Case("1---0000"):  # SUB
                self.ALU(m, ALU8Func.SUB)
            with m.Case("1---0001"):  # CMP
                self.ALU(m, ALU8Func.SUB)
            with m.Case("1---0010"):  # SBC
                self.ALU(m, ALU8Func.SBC)
            with m.Case("1---0100"):  # AND
                self.ALU(m, ALU8Func.AND)
            with m.Case("1---0101"):  # BIT
                self.ALU(m, ALU8Func.AND)
            with m.Case("1---1000"):  # EOR
                self.ALU(m, ALU8Func.EOR)
            with m.Case("1---1001"):  # ADC
                self.ALU(m, ALU8Func.ADC)
            with m.Case("1---1010"):  # ORA
                self.ALU(m, ALU8Func.ORA)
            with m.Case("1---1011"):  # ADD
                self.ALU(m, ALU8Func.ADD)

            with m.Case("1--10111", "1-100111"):  # STA
                self.STA(m)
            with m.Case("101-1101"):  # JSR
                self.JSR_BSR(m)
            with m.Default():  # Illegal
                self.end_instr(m, self.pc)

    def ALU(self, m: Module, func: ALU8Func):
        b = self.instr[6]
        store = ~self.instr[:4].matches("0001", "0101") # CMP and BIT don't store.

        with m.If(self.mode == ModeBits.DIRECT.value):
            operand = self.mode_direct(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.VMA.eq(1)

            with m.If(self.cycle == 2):
                m.d.comb += self.src8_1.eq(Mux(b, self.b, self.a))
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.alu8_func.eq(func)
                with m.If(store):
                    with m.If(b):
                        m.d.ph1 += self.b.eq(self.alu8)
                    with m.Else():
                        m.d.ph1 += self.a.eq(self.alu8)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.VMA.eq(1)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(Mux(b, self.b, self.a))
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.alu8_func.eq(func)
                with m.If(store):
                    with m.If(b):
                        m.d.ph1 += self.b.eq(self.alu8)
                    with m.Else():
                        m.d.ph1 += self.a.eq(self.alu8)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.IMMEDIATE.value):
            operand = self.mode_immediate8(m)

            with m.If(self.cycle == 2):
                m.d.comb += self.src8_1.eq(Mux(b, self.b, self.a))
                m.d.comb += self.src8_2.eq(operand)
                m.d.comb += self.alu8_func.eq(func)
                with m.If(store):
                    with m.If(b):
                        m.d.ph1 += self.b.eq(self.alu8)
                    with m.Else():
                        m.d.ph1 += self.a.eq(self.alu8)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            operand = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.VMA.eq(1)

            with m.If(self.cycle == 4):
                m.d.comb += self.src8_1.eq(Mux(b, self.b, self.a))
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.alu8_func.eq(func)
                with m.If(store):
                    with m.If(b):
                        m.d.ph1 += self.b.eq(self.alu8)
                    with m.Else():
                        m.d.ph1 += self.a.eq(self.alu8)
                self.end_instr(m, self.pc)

    def ALU2(
        self,
        m: Module,
        func: ALU8Func,
        operand1: int,
        operand2: int,
        store: bool = True,
    ):
        with m.If(self.mode == ModeBits.A.value):
            m.d.comb += self.src8_1.eq(Mux(operand1, self.a, 0))
            m.d.comb += self.src8_2.eq(Mux(operand2, self.a, 0))
            m.d.comb += self.alu8_func.eq(func)
            if store:
                m.d.ph1 += self.a.eq(self.alu8)
            self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.B.value):
            m.d.comb += self.src8_1.eq(Mux(operand1, self.b, 0))
            m.d.comb += self.src8_2.eq(Mux(operand2, self.b, 0))
            m.d.comb += self.alu8_func.eq(func)
            if store:
                m.d.ph1 += self.b.eq(self.alu8)
            self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.VMA.eq(1)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(Mux(operand1, self.Din, 0))
                m.d.comb += self.src8_2.eq(Mux(operand2, self.Din, 0))
                m.d.comb += self.alu8_func.eq(func)

                m.d.ph1 += self.tmp16[8:].eq(self.alu8)
                m.d.ph1 += self.VMA.eq(0)
                # Important! save tmp16 to Addr, because we're overwriting
                # its high byte from the ALU result!
                m.d.ph1 += self.Addr.eq(operand) 
                m.d.ph1 += self.RW.eq(1)

            with m.Elif(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(self.Addr)
                m.d.ph1 += self.Dout.eq(self.tmp16[8:])
                m.d.ph1 += self.RW.eq(0)
                if not store:
                    m.d.ph1 += self.VMA.eq(0)

            with m.Elif(self.cycle == 5):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            operand = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.VMA.eq(1)

            with m.If(self.cycle == 4):
                m.d.comb += self.src8_1.eq(Mux(operand1, self.Din, 0))
                m.d.comb += self.src8_2.eq(Mux(operand2, self.Din, 0))
                m.d.comb += self.alu8_func.eq(func)

                m.d.ph1 += self.tmp16[8:].eq(self.alu8)
                m.d.ph1 += self.VMA.eq(0)
                # Important! save tmp16 to Addr, because we're overwriting
                # its high byte from the ALU result!
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 5):
                m.d.ph1 += self.Addr.eq(self.Addr)
                m.d.ph1 += self.Dout.eq(self.tmp16[8:])
                m.d.ph1 += self.RW.eq(0)
                if not store:
                    m.d.ph1 += self.VMA.eq(0)

            with m.If(self.cycle == 6):
                self.end_instr(m, self.pc)

    def BR(self, m: Module):
        operand = self.mode_immediate8(m)

        # Converts 8-bit operand to 16-bit 2's complement signed operand.
        relative = LCat(Repl(operand[7], 8), operand)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.VMA.eq(0)

        # At this point, pc is the instruction start + 2, so we just
        # add the signed relative offset to get the target.
        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16.eq(self.pc + relative)

            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 3):

            take_branch = self.branch_check(m)
            self.end_instr(m, Mux(take_branch, self.tmp16, self.pc))

    def SBA_CBA(self, m: Module):
        m.d.comb += self.src8_1.eq(self.a)
        m.d.comb += self.src8_2.eq(self.b)
        m.d.comb += self.alu8_func.eq(ALU8Func.SUB)
        with m.If(self.instr[0] == 0):
            m.d.ph1 += self.a.eq(self.alu8)
        self.end_instr(m, self.pc)

    def TAB_TBA(self, m: Module):
        with m.If(self.instr[0] == 0):  # TAB
            m.d.comb += self.src8_2.eq(self.a)
            m.d.ph1 += self.b.eq(self.alu8)
        with m.Else():  # TBA
            m.d.comb += self.src8_2.eq(self.b)
            m.d.ph1 += self.a.eq(self.alu8)
        m.d.comb += self.alu8_func.eq(ALU8Func.LD)
        self.end_instr(m, self.pc)

    def ABA(self, m: Module):
        m.d.comb += self.src8_1.eq(self.a)
        m.d.comb += self.src8_2.eq(self.b)
        m.d.comb += self.alu8_func.eq(ALU8Func.ADD)
        m.d.ph1 += self.a.eq(self.alu8)
        self.end_instr(m, self.pc)

    def TSX_TXS(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 3):
            with m.If(self.instr[0] == 0):  # TSX
                m.d.ph1 += self.x.eq(self.sp)
            with m.Else():  # TXS
                m.d.ph1 += self.sp.eq(self.x)
            self.end_instr(m, self.pc)

    def INS_DES(self, m: Module):
        """Increments or decrements S."""
        dec = ~self.instr[0]

        with m.If(self.cycle == 1):
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.Addr.eq(self.sp)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.Addr.eq(Mux(dec, self.Addr - 1, self.Addr + 1))

        with m.If(self.cycle == 3):
            m.d.ph1 += self.sp.eq(self.Addr)
            self.end_instr(m, self.pc)

    def PUL2(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(1)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.sp.eq(self.Addr)
            m.d.comb += self.alu8_func.eq(ALU8Func.NONE)
            m.d.comb += self.src8_1.eq(self.Din)
            with m.If(self.instr[0] == 0):  # PUL A
                m.d.ph1 += self.a.eq(self.alu8)
            with m.Else():
                m.d.ph1 += self.b.eq(self.alu8)
            self.end_instr(m, self.pc)

    def PSH(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.Dout.eq(Mux(self.instr[0] == 0, self.a, self.b))

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.sp.eq(self.Addr)
            self.end_instr(m, self.pc)

    def LDS_LDX(self, m: Module):
        lds = self.instr[6] == 0

        with m.If(self.mode == ModeBits.DIRECT.value):
            _ = self.mode_direct(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(self.Din)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                with m.If(lds):
                    m.d.ph1 += self.sp[8:].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[8:].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 3):
                with m.If(lds):
                    m.d.ph1 += self.sp[:8].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[:8].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                with m.If(lds):
                    m.d.ph1 += self.sp[8:].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[8:].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 4):
                with m.If(lds):
                    m.d.ph1 += self.sp[:8].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[:8].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.IMMEDIATE.value):
            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.ph1 += self.pc.eq(self.pc + 1)
                with m.If(lds):
                    m.d.ph1 += self.sp[8:].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[8:].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 2):
                with m.If(lds):
                    m.d.ph1 += self.sp[:8].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[:8].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc + 1)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            _ = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.tmp16)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                with m.If(lds):
                    m.d.ph1 += self.sp[8:].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[8:].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 5):
                with m.If(lds):
                    m.d.ph1 += self.sp[:8].eq(self.Din)
                with m.Else():
                    m.d.ph1 += self.x[:8].eq(self.Din)
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc)

    def CPX(self, m: Module):
        with m.If(self.mode == ModeBits.DIRECT.value):
            _ = self.mode_direct(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(self.Din)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXHI)
                m.d.comb += self.src8_1.eq(self.x[8:])
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 3):
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXLO)
                m.d.comb += self.src8_1.eq(self.x[:8])
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXHI)
                m.d.comb += self.src8_1.eq(self.x[8:])
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 4):
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXLO)
                m.d.comb += self.src8_1.eq(self.x[:8])
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.IMMEDIATE.value):
            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.ph1 += self.pc.eq(self.pc + 1)
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXHI)
                m.d.comb += self.src8_1.eq(self.x[8:])
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 2):
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXLO)
                m.d.comb += self.src8_1.eq(self.x[:8])
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc + 1)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            _ = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.tmp16)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXHI)
                m.d.comb += self.src8_1.eq(self.x[8:])
                m.d.comb += self.src8_2.eq(self.Din)

            with m.If(self.cycle == 5):
                m.d.comb += self.alu8_func.eq(ALU8Func.CPXLO)
                m.d.comb += self.src8_1.eq(self.x[:8])
                m.d.comb += self.src8_2.eq(self.Din)
                self.end_instr(m, self.pc)

    def STS_STX(self, m: Module):
        sts = self.instr[6] == 0

        with m.If(self.mode == ModeBits.DIRECT.value):
            _ = self.mode_direct(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(self.Din)
                m.d.ph1 += self.VMA.eq(0)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.RW.eq(0)
                with m.If(sts):
                    m.d.comb += self.src8_2.eq(self.sp[8:])
                with m.Else():
                    m.d.comb += self.src8_2.eq(self.x[8:])
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                with m.If(sts):
                    m.d.comb += self.src8_2.eq(self.sp[:8])
                with m.Else():
                    m.d.comb += self.src8_2.eq(self.x[:8])
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 4):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.VMA.eq(0)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.RW.eq(0)
                with m.If(sts):
                    m.d.comb += self.src8_2.eq(self.sp[8:])
                with m.Else():
                    m.d.comb += self.src8_2.eq(self.x[8:])
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                with m.If(sts):
                    m.d.comb += self.src8_2.eq(self.sp[:8])
                with m.Else():
                    m.d.comb += self.src8_2.eq(self.x[:8])
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 5):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            _ = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.tmp16)
                m.d.ph1 += self.VMA.eq(0)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.RW.eq(0)
                with m.If(sts):
                    m.d.comb += self.src8_2.eq(self.sp[8:])
                with m.Else():
                    m.d.comb += self.src8_2.eq(self.x[8:])
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 5):
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(self.Addr + 1)
                with m.If(sts):
                    m.d.comb += self.src8_2.eq(self.sp[:8])
                with m.Else():
                    m.d.comb += self.src8_2.eq(self.x[:8])
                m.d.comb += self.alu8_func.eq(ALU8Func.LDCHAIN)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 6):
                self.end_instr(m, self.pc)

    def RTS(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(1)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(1)

        with m.If(self.cycle == 4):
            m.d.ph1 += self.sp.eq(self.Addr)
            self.end_instr(m, LCat(self.tmp16[8:], self.Din))

    def BSR(self, m: Module):
        operand = self.mode_immediate8(m)

        # Converts 8-bit operand to 16-bit 2's complement signed operand.
        relative = LCat(Repl(operand[7], 8), operand)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.VMA.eq(0)

        # At this point, pc is the instruction start + 2, so we just
        # add the signed relative offset to get the target.
        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16.eq(self.pc + relative)

            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.pc[:8])

        with m.If(self.cycle == 3):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.pc[8:])

        with m.If(self.cycle == 4):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 5):
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.sp.eq(self.Addr)

        with m.If(self.cycle == 6):
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.Addr.eq(self.tmp16)

        with m.If(self.cycle == 7):
            self.end_instr(m, self.tmp16)

    def JSR_BSR(self, m: Module):
        with m.If(self.instr.matches("10001101")):
            self.BSR(m)

        with m.Elif(self.instr[4] == 1):  # extended
            _ = self.mode_ext(m)  # output is in tmp16 on cycle 3

            with m.If(self.cycle == 2):
                # TODO: needs to be checked
                m.d.ph1 += self.VMA.eq(0)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.sp)
                m.d.ph1 += self.VMA.eq(1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.pc[:8])

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.VMA.eq(1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.pc[8:])

            with m.If(self.cycle == 5):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 6):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.sp.eq(self.Addr)

            with m.If(self.cycle == 7):
                # TODO: needs to be checked
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(self.tmp16)

            with m.If(self.cycle == 8):
                self.end_instr(m, self.tmp16)

        with m.Else():  # indexed
            _ = self.mode_indexed(m)  # output is in tmp16 on cycle 3

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(self.sp)
                m.d.ph1 += self.VMA.eq(1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.pc[:8])

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.VMA.eq(1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(self.pc[8:])

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(self.Addr - 1)
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 5):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.sp.eq(self.Addr)

            with m.If(self.cycle == 6):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(self.tmp16)

            with m.If(self.cycle == 7):
                self.end_instr(m, self.tmp16)

    def SWI(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.pc[:8])

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.pc[8:])

        with m.If(self.cycle == 3):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.x[:8])

        with m.If(self.cycle == 4):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.x[8:])

        with m.If(self.cycle == 5):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.a)

        with m.If(self.cycle == 6):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.b)

        with m.If(self.cycle == 7):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.ccs)

        with m.If(self.cycle == 8):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 9):
            m.d.ph1 += self.sp.eq(self.Addr)
            m.d.comb += self.alu8_func.eq(ALU8Func.SEI)
            m.d.ph1 += self.Addr.eq(0xFFFA)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 10):
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 11):
            self.end_instr(m, LCat(self.tmp16[8:], self.Din))

    def WAI(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.pc[:8])

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.pc[8:])

        with m.If(self.cycle == 3):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.x[:8])

        with m.If(self.cycle == 4):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.x[8:])

        with m.If(self.cycle == 5):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.a)

        with m.If(self.cycle == 6):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.b)

        with m.If(self.cycle == 7):
            m.d.ph1 += self.Addr.eq(self.Addr - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(self.ccs)

        with m.If(self.cycle == 8):
            m.d.ph1 += self.sp.eq(self.Addr)
            m.d.comb += self.wai.eq(1)
            self.end_instr(m, self.pc)

    def RTI(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.Addr.eq(self.sp)
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            m.d.comb += self.alu8_func.eq(ALU8Func.SEF)
            m.d.comb += self.src8_1.eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 4):
            m.d.comb += self.alu8_func.eq(ALU8Func.NONE)
            m.d.comb += self.src8_1.eq(self.Din)
            m.d.ph1 += self.b.eq(self.alu8)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 5):
            m.d.comb += self.alu8_func.eq(ALU8Func.NONE)
            m.d.comb += self.src8_1.eq(self.Din)
            m.d.ph1 += self.a.eq(self.alu8)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 6):
            m.d.ph1 += self.x[8:].eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 7):
            m.d.ph1 += self.x[:8].eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 8):
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.VMA.eq(1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 9):
            m.d.ph1 += self.sp.eq(self.Addr)
            self.end_instr(m, LCat(self.tmp16[8:], self.Din))

    def DAA(self, m: Module):
        m.d.comb += self.src8_1.eq(self.a)
        m.d.comb += self.alu8_func.eq(ALU8Func.DAA)
        m.d.ph1 += self.a.eq(self.alu8)
        self.end_instr(m, self.pc)

    def CL_SE_C(self, m: Module):
        """Clears or sets Carry."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(
                Mux(self.instr[0], ALU8Func.SEC, ALU8Func.CLC)
            )
            self.end_instr(m, self.pc)

    def CL_SE_V(self, m: Module):
        """Clears or sets Overflow."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(
                Mux(self.instr[0], ALU8Func.SEV, ALU8Func.CLV)
            )
            self.end_instr(m, self.pc)

    def CL_SE_I(self, m: Module):
        """Clears or sets Interrupt."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(
                Mux(self.instr[0], ALU8Func.SEI, ALU8Func.CLI)
            )
            self.end_instr(m, self.pc)

    def IN_DE_X(self, m: Module):
        """Increments or decrements X."""
        dec = self.instr[0]

        with m.If(self.cycle == 1):
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.Addr.eq(self.x)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.VMA.eq(0)
            m.d.ph1 += self.Addr.eq(Mux(dec, self.Addr - 1, self.Addr + 1))

        with m.If(self.cycle == 3):
            m.d.ph1 += self.x.eq(self.Addr)
            m.d.comb += self.alu8_func.eq(Mux(self.Addr == 0, ALU8Func.SEZ, ALU8Func.CLZ))
            self.end_instr(m, self.pc)

    def JMP(self, m: Module):
        with m.If(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                self.end_instr(m, operand)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            operand = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                self.end_instr(m, operand)

    def NOP(self, m: Module):
        self.end_instr(m, self.pc)

    def STA(self, m: Module):
        b = self.instr[6]

        with m.If(self.mode == ModeBits.DIRECT.value):
            operand = self.mode_direct(m)

            with m.If(self.cycle == 1):
                # Output during cycle 2:
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                # Output during cycle 3:
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(Mux(b, self.b, self.a))
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_2.eq(Mux(b, self.b, self.a))
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.EXTENDED.value):
            operand = self.mode_ext(m)

            with m.If(self.cycle == 2):
                # Output during cycle 3:
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                # Output during cycle 4:
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(Mux(b, self.b, self.a))
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                m.d.comb += self.src8_2.eq(Mux(b, self.b, self.a))
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode == ModeBits.INDEXED.value):
            operand = self.mode_indexed(m)

            with m.If(self.cycle == 3):
                # Output during cycle 4:
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 4):
                # Output during cycle 5:
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(Mux(b, self.b, self.a))
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 5):
                m.d.comb += self.src8_2.eq(Mux(b, self.b, self.a))
                m.d.comb += self.alu8_func.eq(ALU8Func.LD)
                self.end_instr(m, self.pc)

    def TAP(self, m: Module):
        """Transfer A to CCS."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(ALU8Func.TAP)
            m.d.comb += self.src8_1.eq(self.a)
            self.end_instr(m, self.pc)

    def TPA(self, m: Module):
        """Transfer CCS to A."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(ALU8Func.TPA)
            m.d.ph1 += self.a.eq(self.alu8)
            self.end_instr(m, self.pc)

    def branch_check(self, m: Module) -> Signal:
        """Generates logic for a 1-bit value for branching.

        Returns a 1-bit Signal which is set if the branch should be
        taken. The branch logic is determined by the instruction.
        """
        invert = self.instr[0]
        cond = Signal()
        take_branch = Signal()

        with m.Switch(self.instr[1:4]):
            with m.Case("000"):  # BRA, BRN
                m.d.comb += cond.eq(1)
            with m.Case("001"):  # BHI, BLS
                m.d.comb += cond.eq(~(self.ccs[Flags.C] | self.ccs[Flags.Z]))
            with m.Case("010"):  # BCC, BCS
                m.d.comb += cond.eq(~self.ccs[Flags.C])
            with m.Case("011"):  # BNE, BEQ
                m.d.comb += cond.eq(~self.ccs[Flags.Z])
            with m.Case("100"):  # BVC, BVS
                m.d.comb += cond.eq(~self.ccs[Flags.V])
            with m.Case("101"):  # BPL, BMI
                m.d.comb += cond.eq(~self.ccs[Flags.N])
            with m.Case("110"):  # BGE, BLT
                m.d.comb += cond.eq(~(self.ccs[Flags.N] ^ self.ccs[Flags.V]))
            with m.Case("111"):  # BGT, BLE
                m.d.comb += cond.eq(
                    ~(self.ccs[Flags.Z] | (self.ccs[Flags.N] ^ self.ccs[Flags.V]))
                )

        m.d.comb += take_branch.eq(cond ^ invert)
        return take_branch

    def mode_immediate8(self, m: Module) -> Statement:
        """Generates logic to get the 8-bit operand for immediate mode instructions.

        Returns a Statement containing an 8-bit operand.
        After cycle 1, tmp16[8:] contains the operand.
        """
        operand = Mux(self.cycle == 1, self.Din, self.tmp16[8:])

        with m.If(self.cycle == 1):
            # Here Addr = instr + 1 and pc = instr + 1
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.Addr.eq(self.Addr + 1)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(1)

        return operand

    def mode_direct(self, m: Module) -> Statement:
        """Generates logic to get the 8-bit zero-page address for direct mode instructions.

        Returns a Statement containing a 16-bit address where the upper byte is zero.
        After cycle 1, tmp16 contains the address.
        """
        operand = Mux(self.cycle == 1, self.Din, self.tmp16)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16[8:].eq(0)
            m.d.ph1 += self.tmp16[:8].eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(1)

        return operand

    def mode_indexed(self, m: Module) -> Statement:
        """Generates logic to get the 16-bit address for indexed mode instructions.

        Returns a Statement containing a 16-bit address.
        After cycle 2, tmp16 contains the address. The address is not valid until after
        cycle 2.
        """
        operand = self.tmp16

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16[8:].eq(0)
            m.d.ph1 += self.tmp16[:8].eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(0)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16.eq(self.tmp16 + self.x)
            m.d.ph1 += self.VMA.eq(0)

        return operand

    def mode_ext(self, m: Module) -> Statement:
        """Generates logic to get the 16-bit address for extended mode instructions.

        Returns a Statement containing the 16-bit address. After cycle 2, tmp16 
        contains the address.
        """
        operand = Mux(self.cycle == 2, LCat(self.tmp16[8:], self.Din), self.tmp16)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.VMA.eq(1)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16[:8].eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.VMA.eq(1)

        return operand

    def end_instr(self, m: Module, addr: Statement):
        """Ends the instruction.

        Loads the PC and Addr register with the given addr, sets R/W mode
        to read, and sets the cycle to 0 at the end of the current cycle.
        """
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
            m.d.ph1 += Cover(core.formalData.snapshot_taken & core.end_instr_flag)
            m.d.ph1 += Assume(core.formalData.snapshot_taken & core.end_instr_flag)

        # Verify reset does what it's supposed to
        with m.If(
            Past(rst, 4) & ~Past(rst, 3) & ~Past(rst, 2) & ~Past(rst) & ~Past(core.NMI)
        ):
            m.d.ph1 += Assert(Past(core.Addr, 2) == 0xFFFE)
            m.d.ph1 += Assert(Past(core.Addr) == 0xFFFF)
            m.d.ph1 += Assert(core.Addr[8:] == Past(core.Din, 2))
            m.d.ph1 += Assert(core.Addr[:8] == Past(core.Din))
            m.d.ph1 += Assert(core.Addr == core.pc)

        main_runner(parser, args, m, ports=core.ports() + [ph1clk, rst])

    else:
        # Fake memory
        mem = {
            0xFFFC: 0xF0,
            0xFFFD: 0xF0,
            0xFFFE: 0x12,
            0xFFFF: 0x34,
            0x1234: 0x20,  # BRA 0x1236
            0x1235: 0x00,
            0x1236: 0x3E,  # WAI
            0x1237: 0x01,  # NOP
            0xF0F0: 0x01,  # NOP
            0xF0F1: 0x01,  # NOP
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
            for _ in range(20):
                yield
            yield core.NMI.eq(1)
            yield
            yield core.NMI.eq(0)
            for _ in range(20):
                yield

        sim.add_sync_process(process, domain="ph1")
        with sim.write_vcd("test.vcd", "test.gtkw", traces=core.ports()):
            sim.run()
