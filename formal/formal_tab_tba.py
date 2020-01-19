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
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(TAB, TBA)

    def check(self, m: Module):
        self.assert_cycles(m, 2)
        input = Mux(self.instr[0] == 0, self.data.pre_a, self.data.pre_b)

        with m.If(self.instr.matches(TAB)):
            self.assert_registers(m, B=self.data.pre_a, PC=self.data.pre_pc + 1)
        with m.Else():
            self.assert_registers(m, A=self.data.pre_b, PC=self.data.pre_pc + 1)

        z = input == 0
        n = input[7]
        v = 0

        self.assert_flags(m, Z=z, N=n, V=v)
