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

from nmigen import Signal, Value, Cat, Module, Mux
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from consts.consts import Flags
from .alu_verification import AluVerification


class Formal(AluVerification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("1---00-0")

    def check(self, m: Module, instr: Value, data: FormalData):
        input1, input2, actual_output = self.common_check(m, instr, data)

        carry_in = Signal()
        sum9 = Signal(9)
        sum8 = Signal(8)
        with_carry = (instr[1] == 1)

        n = sum9[7]
        c = ~sum9[8]
        z = (sum9[:8] == 0)
        v = (sum8[7] ^ sum9[8])

        with m.If(with_carry):
            m.d.comb += carry_in.eq(data.pre_ccs[Flags.C])
        with m.Else():
            m.d.comb += carry_in.eq(0)

        m.d.comb += [
            sum9.eq(input1 + ~input2 + ~carry_in),
            sum8.eq(input1[:7] + ~input2[:7] + ~carry_in),
            Assert(actual_output == sum9[:8]),
        ]
        self.assertFlags(m, data.post_ccs, data.pre_ccs,
                         Z=z, N=n, V=v, C=c)
