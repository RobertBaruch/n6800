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
from consts.consts import ModeBits


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("0011011-")

    def check(self, m: Module):
        push_a = self.instr[0] == 0

        self.assert_cycles(m, 4)
        self.assert_cycle_signals(m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0)
        data = self.assert_cycle_signals(
            m, 2, address=self.data.pre_sp, vma=1, rw=0, ba=0
        )
        self.assert_cycle_signals(m, 3, vma=0, ba=0)

        with m.If(push_a):
            m.d.comb += Assert(data == self.data.pre_a)
        with m.Else():
            m.d.comb += Assert(data == self.data.pre_b)

        self.assert_registers(m, SP=self.data.pre_sp - 1, PC=self.data.pre_pc + 1)
        self.assert_flags(m)
