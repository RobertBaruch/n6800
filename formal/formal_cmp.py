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

from nmigen import Signal, Value, Cat, Module, signed, Mux
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from .alu_verification import AluVerification


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("1---0001")

    def check(self, m: Module):
        input1, input2, actual_output, size, use_a = self.common_check(m)
        sinput1 = Signal(signed(8))
        sinput2 = Signal(signed(8))
        m.d.comb += sinput1.eq(input1)
        m.d.comb += sinput2.eq(input2)

        z = (input1 == input2)
        n = (input1 - input2)[7]

        # The following is wrong. This would calculate LT (less than), not N.
        # In other words, N is not a comparison, it's just the high bit
        # of the (unsigned) result.
        # n = ((sinput1 - sinput2) < 0)

        # GE is true if and only if N^V==0 (i.e. N == V).
        ge = sinput1 >= sinput2
        v = Mux(ge, n, ~n)
        c = (input1 < input2)

        self.assert_registers(m, PC=self.data.pre_pc+size)
        self.assert_flags(m, Z=z, N=n, V=v, C=c)
