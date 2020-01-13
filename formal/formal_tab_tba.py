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


TAB = "00010010"
TBA = "00010011"


class Formal(Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(TAB, TBA)

    def check(self, m: Module, instr: Value, data: FormalData):
        m.d.comb += [
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_read == 0),
            Assert(data.addresses_written == 0),
        ]
        m.d.comb += Assert(data.post_pc == data.plus16(data.pre_pc, 1)),

        input = Mux(instr[0] == 0, data.pre_a, data.pre_b)
        output = Mux(instr[0] == 0, data.post_b, data.post_a)
        m.d.comb += Assert(input == output)

        with m.If(instr.matches(TAB)):
            m.d.comb += Assert(data.post_a == data.pre_a)
        with m.Else():
            m.d.comb += Assert(data.post_b == data.pre_b)

        z = (input == 0)
        n = input[7]
        v = 0

        self.assertFlags(m, data.post_ccs, data.pre_ccs,
                         Z=z, N=n, V=v)
