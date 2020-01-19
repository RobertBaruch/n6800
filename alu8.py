# alu8.py: 8-bit ALU for the 6800 CPU
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

from enum import IntEnum
from typing import List, Dict, Tuple, Optional

from consts.consts import Flags

from nmigen import Signal, Value, Elaboratable, Module, Cat, Const, Mux
from nmigen import ClockDomain, ClockSignal
from nmigen.build import Platform
from nmigen.cli import main_parser, main_runner
from nmigen.asserts import Assert, Assume, Cover, Past


class ALU8Func(IntEnum):
    NONE = 0
    LD = 1
    ADD = 2
    ADC = 3
    SUB = 4
    SBC = 5
    AND = 6
    # BIT is the same as AND, just don't store the output.
    # CMP is the same as SUB, just don't store the output.
    EOR = 7
    ORA = 8
    CLV = 9
    SEV = 10
    CLC = 11
    SEC = 12
    TAP = 13
    TPA = 14
    CLI = 15
    SEI = 16
    CLZ = 17
    SEZ = 18
    COM = 19  # Not implemented using SUB or EOR
    INC = 20  # Not implemented using ADD
    DEC = 21  # Not implemented using SUB
    ROL = 22
    ROR = 23
    ASL = 24
    ASR = 25
    LSR = 26
    DAA = 27
    # LDCHAIN assumes the high byte of a 16-bit value has already
    # been passed through LD, so N and Z have been evaluated. LDCHAIN
    # is then used on the low byte, so N should not be changed, and
    # Z should be anded with low_byte == 0.
    LDCHAIN = 28
    # CPXHI is the same as SUB, but doesn't set the C flag.
    CPXHI = 29
    # CPXLO assumes the high byte of a 16-bit value has already
    # been passed through CPXHI, so N, V, and Z have been evaluated.
    # Z should be anded with whether the subtraction is zero.
    CPXLO = 30
    SEF = 31  # Set all flags


def LCat(*args) -> Value:
    """Left or logical concatenation.

    Concatenates arguments such that the first argument is placed in the
    highest bit positions, and the last is placed in the lowest bit positions.
    """
    return Cat(*args[::-1])


class ALU8(Elaboratable):
    def __init__(self):
        self.input1 = Signal(8)
        self.input2 = Signal(8)
        self.output = Signal(8)
        self.func = Signal(ALU8Func)

        self.ccs = Signal(8, reset=0b11010000)
        self._ccs = Signal(8)

    def input_ports(self) -> List[Signal]:
        return [self.input1, self.input2, self.func]

    def elaborate(self, platform: Platform) -> Module:
        m = Module()

        m.d.comb += self._ccs.eq(self.ccs)
        m.d.ph1 += self.ccs.eq(self._ccs)

        # intermediates
        carry4 = Signal()
        carry7 = Signal()
        carry8 = Signal()
        overflow = Signal()

        with m.Switch(self.func):
            with m.Case(ALU8Func.LD):
                m.d.comb += self.output.eq(self.input2)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(0)

            with m.Case(ALU8Func.LDCHAIN):
                m.d.comb += self.output.eq(self.input2)
                m.d.comb += self._ccs[Flags.Z].eq(
                    (self.output == 0) & self.ccs[Flags.Z])
                m.d.comb += self._ccs[Flags.V].eq(0)

            with m.Case(ALU8Func.ADD, ALU8Func.ADC):
                carry_in = Mux(self.func == ALU8Func.ADD, 0, self.ccs[Flags.C])

                sum0_3 = Cat(self.output[:4], carry4)
                m.d.comb += sum0_3.eq(self.input1[:4] +
                                      self.input2[:4] + carry_in)
                sum4_6 = Cat(self.output[4:7], carry7)
                m.d.comb += sum4_6.eq(self.input1[4:7] +
                                      self.input2[4:7] + carry4)
                sum7 = Cat(self.output[7], carry8)
                m.d.comb += sum7.eq(self.input1[7] + self.input2[7] + carry7)
                m.d.comb += overflow.eq(carry7 ^ carry8)
                m.d.comb += self._ccs[Flags.H].eq(carry4)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.V].eq(overflow)
                m.d.comb += self._ccs[Flags.C].eq(carry8)

            with m.Case(ALU8Func.SUB, ALU8Func.SBC, ALU8Func.CPXHI, ALU8Func.CPXLO):
                carry_in = Mux(self.func != ALU8Func.SBC, 0, self.ccs[Flags.C])

                sum0_6 = Cat(self.output[:7], carry7)
                m.d.comb += sum0_6.eq(self.input1[:7] +
                                      ~self.input2[:7] + ~carry_in)
                sum7 = Cat(self.output[7], carry8)
                m.d.comb += sum7.eq(self.input1[7] + ~self.input2[7] + carry7)
                m.d.comb += overflow.eq(carry7 ^ carry8)

                with m.If(self.func != ALU8Func.CPXLO):
                    m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                    m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                    m.d.comb += self._ccs[Flags.V].eq(overflow)
                    with m.If(self.func != ALU8Func.CPXHI):
                        m.d.comb += self._ccs[Flags.C].eq(~carry8)
                with m.Else():
                    m.d.comb += self._ccs[Flags.Z].eq(
                        (self.output == 0) & self.ccs[Flags.Z])

            with m.Case(ALU8Func.AND):
                m.d.comb += self.output.eq(self.input1 & self.input2)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(0)

            with m.Case(ALU8Func.EOR):
                m.d.comb += self.output.eq(self.input1 ^ self.input2)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(0)

            with m.Case(ALU8Func.ORA):
                m.d.comb += self.output.eq(self.input1 | self.input2)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(0)

            with m.Case(ALU8Func.INC):
                m.d.comb += self.output.eq(self.input2 + 1)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(self.output == 0x80)

            with m.Case(ALU8Func.DEC):
                m.d.comb += self.output.eq(self.input2 - 1)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(self.output == 0x7F)

            with m.Case(ALU8Func.COM):
                m.d.comb += self.output.eq(0xFF ^ self.input2)
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.V].eq(0)
                m.d.comb += self._ccs[Flags.C].eq(1)

            with m.Case(ALU8Func.ROL):
                # IIIIIIIIC ->
                # COOOOOOOO
                m.d.comb += [
                    LCat(self._ccs[Flags.C], self.output).eq(
                        LCat(self.input2, self.ccs[Flags.C])),
                    self._ccs[Flags.Z].eq(self.output == 0),
                    self._ccs[Flags.N].eq(self.output[7]),
                    self._ccs[Flags.V].eq(
                        self._ccs[Flags.N] ^ self._ccs[Flags.C])
                ]

            with m.Case(ALU8Func.ROR):
                # CIIIIIIII ->
                # OOOOOOOOC
                m.d.comb += [
                    LCat(self.output, self._ccs[Flags.C]).eq(
                        LCat(self.ccs[Flags.C], self.input2)),
                    self._ccs[Flags.Z].eq(self.output == 0),
                    self._ccs[Flags.N].eq(self.output[7]),
                    self._ccs[Flags.V].eq(
                        self._ccs[Flags.N] ^ self._ccs[Flags.C])
                ]

            with m.Case(ALU8Func.ASL):
                # IIIIIIII0 ->
                # COOOOOOOO
                m.d.comb += [
                    LCat(self._ccs[Flags.C], self.output).eq(
                        LCat(self.input2, Const(0))),
                    self._ccs[Flags.Z].eq(self.output == 0),
                    self._ccs[Flags.N].eq(self.output[7]),
                    self._ccs[Flags.V].eq(
                        self._ccs[Flags.N] ^ self._ccs[Flags.C])
                ]

            with m.Case(ALU8Func.ASR):
                # 7IIIIIIII ->  ("7" is the repeat of input[7])
                # OOOOOOOOC
                m.d.comb += [
                    LCat(self.output, self._ccs[Flags.C]).eq(
                        LCat(self.input2[7], self.input2)),
                    self._ccs[Flags.Z].eq(self.output == 0),
                    self._ccs[Flags.N].eq(self.output[7]),
                    self._ccs[Flags.V].eq(
                        self._ccs[Flags.N] ^ self._ccs[Flags.C])
                ]

            with m.Case(ALU8Func.LSR):
                # 0IIIIIIII ->
                # OOOOOOOOC
                m.d.comb += [
                    LCat(self.output, self._ccs[Flags.C]).eq(
                        LCat(Const(0), self.input2)),
                    self._ccs[Flags.Z].eq(self.output == 0),
                    self._ccs[Flags.N].eq(self.output[7]),
                    self._ccs[Flags.V].eq(
                        self._ccs[Flags.N] ^ self._ccs[Flags.C])
                ]

            with m.Case(ALU8Func.CLC):
                m.d.comb += self._ccs[Flags.C].eq(0)

            with m.Case(ALU8Func.SEC):
                m.d.comb += self._ccs[Flags.C].eq(1)

            with m.Case(ALU8Func.CLV):
                m.d.comb += self._ccs[Flags.V].eq(0)

            with m.Case(ALU8Func.SEV):
                m.d.comb += self._ccs[Flags.V].eq(1)

            with m.Case(ALU8Func.CLI):
                m.d.comb += self._ccs[Flags.I].eq(0)

            with m.Case(ALU8Func.SEI):
                m.d.comb += self._ccs[Flags.I].eq(1)

            with m.Case(ALU8Func.CLZ):
                m.d.comb += self._ccs[Flags.Z].eq(0)

            with m.Case(ALU8Func.SEZ):
                m.d.comb += self._ccs[Flags.Z].eq(1)

            with m.Case(ALU8Func.TAP):
                m.d.comb += self._ccs.eq(self.input1 | 0b11000000)

            with m.Case(ALU8Func.TPA):
                m.d.comb += self.output.eq(self.ccs | 0b11000000)

            with m.Case(ALU8Func.SEF):
                m.d.comb += self._ccs.eq(self.input1 | 0b11000000)

            with m.Case(ALU8Func.DAA):
                adjust = Signal(8)
                low = self.input1[:4]
                high = self.input1[4:]
                low_ten_or_more = low >= 0xA
                high_ten_or_more = high >= 0xA

                with m.If(low_ten_or_more | self.ccs[Flags.H]):
                    m.d.comb += adjust[:4].eq(6)
                with m.If(high_ten_or_more | self.ccs[Flags.C] | (low_ten_or_more & (high == 9))):
                    m.d.comb += adjust[4:].eq(6)
                sum9 = LCat(carry8, self.output)

                m.d.comb += sum9.eq(self.input1 + adjust)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.C].eq(carry8 | self.ccs[Flags.C])

        return m


if __name__ == "__main__":
    parser = main_parser()
    args = parser.parse_args()

    m = Module()
    m.submodules.alu = alu = ALU8()
    m.domains.ph1 = ph1 = ClockDomain("ph1")

    rst = Signal()
    ph1clk = ClockSignal("ph1")
    ph1.rst = rst

    test_daa = Signal()
    m.submodules.alu2 = alu2 = ALU8()

    carry_in = Signal()
    sum9 = Signal(9)
    sum8 = Signal(8)
    sum5 = Signal(5)

    m.d.ph1 += Assume(rst == 0)
    m.d.comb += Assert(alu._ccs[6:] == 0b11)

    with m.If((~test_daa) | ~Past(test_daa)):
        with m.Switch(alu.func):
            with m.Case(ALU8Func.ADD, ALU8Func.ADC):
                # sumN = input1[:N] + input2[:N] (so sumN[N-1] is the carry bit)
                with m.If(alu.func == ALU8Func.ADD):
                    m.d.comb += carry_in.eq(0)
                with m.Else():
                    m.d.comb += carry_in.eq(alu.ccs[Flags.C])
                h = sum5[4]
                n = sum9[7]
                c = sum9[8]
                z = (sum9[:8] == 0)
                v = (sum8[7] ^ c)
                m.d.comb += [
                    sum9.eq(alu.input1 + alu.input2 + carry_in),
                    sum8.eq(alu.input1[:7] + alu.input2[:7] + carry_in),
                    sum5.eq(alu.input1[:4] + alu.input2[:4] + carry_in),
                    Assert(alu.output == sum9[:8]),
                    Assert(alu._ccs[Flags.H] == h),
                    Assert(alu._ccs[Flags.N] == n),
                    Assert(alu._ccs[Flags.Z] == z),
                    Assert(alu._ccs[Flags.V] == v),
                    Assert(alu._ccs[Flags.C] == c),
                    Assert(alu._ccs[Flags.I] == alu.ccs[Flags.I]),
                ]
            with m.Case(ALU8Func.SUB, ALU8Func.SBC):
                with m.If(alu.func == ALU8Func.SUB):
                    m.d.comb += carry_in.eq(0)
                with m.Else():
                    m.d.comb += carry_in.eq(alu.ccs[Flags.C])
                n = sum9[7]
                c = ~sum9[8]
                z = (sum9[:8] == 0)
                v = (sum8[7] ^ sum9[8])
                m.d.comb += [
                    sum9.eq(alu.input1 + ~alu.input2 + ~carry_in),
                    sum8.eq(alu.input1[:7] + ~alu.input2[:7] + ~carry_in),
                    Assert(sum9[:8] == (
                        alu.input1 - alu.input2 - carry_in)[:8]),
                    Assert(alu.output == sum9[:8]),
                    Assert(alu._ccs[Flags.N] == n),
                    Assert(alu._ccs[Flags.Z] == z),
                    Assert(alu._ccs[Flags.V] == v),
                    Assert(alu._ccs[Flags.C] == c),
                    Assert(alu._ccs[Flags.H] == alu.ccs[Flags.H]),
                    Assert(alu._ccs[Flags.I] == alu.ccs[Flags.I]),
                ]

    with m.Else():  # test_daa
        in1_lo = Past(alu.input1)[:4]
        in1_hi = Past(alu.input1)[4:]
        in2_lo = Past(alu.input2)[:4]
        in2_hi = Past(alu.input2)[4:]
        in_carry = Past(alu.ccs)[Flags.C]
        out_lo = alu.output[:4]
        out_hi = alu.output[4:]
        out_carry = alu._ccs[Flags.C]

        in1_dec = 10 * in1_hi + in1_lo
        in2_dec = 10 * in2_hi + in2_lo
        out_dec = 100 * out_carry + 10 * out_hi + out_lo

        m.d.ph1 += [
            Assume(Past(alu.func) == ALU8Func.ADC),
            Assume(alu.func == ALU8Func.DAA),
            Assume(alu.input1 == Past(alu.output)),
            Assume(in1_lo < 10),
            Assume(in1_hi < 10),
            Assume(in2_lo < 10),
            Assume(in2_hi < 10),
        ]

        m.d.ph1 += [
            Assert((in1_dec + in2_dec + in_carry) == out_dec),
            Assert(alu._ccs[Flags.N] == alu.output[7]),
            Assert(alu._ccs[Flags.Z] == (alu.output == 0)),
        ]

        m.d.ph1 += Cover(out_dec == 142)

    main_runner(parser, args, m, ports=alu.input_ports() +
                alu2.input_ports() + [ph1clk, rst, test_daa])
