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


class Formal(Alu2Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("01--0000")

    def check(self, m: Module):
        input, actual_output = self.common_check(m)
        expected_output = (0 - input)[:8]

        m.d.comb += Assert(expected_output == actual_output)
        n = expected_output[7]
        z = (expected_output == 0)
        v = (expected_output == 0x80)
        c = (expected_output != 0)
        self.assert_flags(m, Z=z, N=n, V=v, C=c)
