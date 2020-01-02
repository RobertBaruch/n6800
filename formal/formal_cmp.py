# Copyright (C) 2019 Robert Baruch <robert.c.baruch@gmail.com>
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

# Flag
_C = 0


class Formal(Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("1-110001")

    def check(self, m: Module, instr: Value, data: FormalData):
        b = instr[6]
        pre_input = Mux(b, data.pre_b, data.pre_a)

        m.d.comb += [
            Assert(data.post_a == data.pre_a),
            Assert(data.post_b == data.pre_b),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_written == 0),
        ]
        m.d.comb += [
            Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
            Assert(data.addresses_read == 3),
            Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
            Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
            Assert(
                data.read_addr[2] == Cat(data.read_data[1], data.read_data[0])),
        ]

        input1 = pre_input
        input2 = data.read_data[2]
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

        self.assertFlags(m, data.post_ccs, data.pre_ccs,
                         Z=z, N=n, V=v, C=c)
