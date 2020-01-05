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

INX = "00001000"
DEX = "00001001"


class Formal(Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(INX, DEX)

    def check(self, m: Module, instr: Value, data: FormalData):
        m.d.comb += [
            Assert(data.post_a == data.pre_a),
            Assert(data.post_b == data.pre_b),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_written == 0),
            Assert(data.addresses_read == 0),
        ]
        m.d.comb += Assert(data.post_pc == data.plus16(data.pre_pc, 1))

        with m.If(instr.matches(INX)):
            m.d.comb += Assert(data.post_x == (data.pre_x + 1)[:16])
        with m.If(instr.matches(DEX)):
            m.d.comb += Assert(data.post_x == (data.pre_x - 1)[:16])

        self.assertFlags(m, data.post_ccs, data.pre_ccs, Z=(data.post_x == 0))
