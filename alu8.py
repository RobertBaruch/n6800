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
from nmigen.asserts import Assert, Assume


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

            with m.Case(ALU8Func.SUB, ALU8Func.SBC):
                carry_in = Mux(self.func == ALU8Func.SUB, 0, self.ccs[Flags.C])

                sum0_6 = Cat(self.output[:7], carry7)
                m.d.comb += sum0_6.eq(self.input1[:7] +
                                      ~self.input2[:7] + ~carry_in)
                sum7 = Cat(self.output[7], carry8)
                m.d.comb += sum7.eq(self.input1[7] + ~self.input2[7] + carry7)
                m.d.comb += overflow.eq(carry7 ^ carry8)
                m.d.comb += self._ccs[Flags.N].eq(self.output[7])
                m.d.comb += self._ccs[Flags.Z].eq(self.output == 0)
                m.d.comb += self._ccs[Flags.V].eq(overflow)
                m.d.comb += self._ccs[Flags.C].eq(~carry8)

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

    carry_in = Signal()
    sum9 = Signal(9)
    sum8 = Signal(8)
    sum5 = Signal(5)

    m.d.comb += Assert(alu._ccs[6:] == 0b11)

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

    main_runner(parser, args, m, ports=alu.input_ports() + [ph1clk, rst])
