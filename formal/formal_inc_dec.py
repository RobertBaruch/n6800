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
from .verification import FormalData
from .alu_verification import Alu2Verification

INC = "01--1100"
DEC = "01--1010"


class Formal(Alu2Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(INC, DEC)

    def check(self, m: Module, instr: Value, data: FormalData):
        input, actual_output = self.common_check(m, instr, data)
        expected_output = Signal(8)

        with m.If(instr.matches(INC)):
            m.d.comb += expected_output.eq((input + 1)[:8])
        with m.If(instr.matches(DEC)):
            m.d.comb += expected_output.eq((input - 1)[:8])

        m.d.comb += Assert(expected_output == actual_output)
        z = (expected_output == 0)
        n = expected_output[7]
        v = Mux(instr.matches(INC), expected_output ==
                0x80, expected_output == 0x7F)

        self.assertFlags(m, data.post_ccs, data.pre_ccs, Z=z, N=n, V=v)
