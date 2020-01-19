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

from nmigen import Signal, Value, Cat, Module, Mux, signed
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification, LCat


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("10001101")

    def check(self, m: Module):
        ret_addr = (self.data.pre_pc + 2)[:16]
        offset = Signal(signed(8))

        self.assert_cycles(m, 8)
        data = self.assert_cycle_signals(
            m, 1, address=self.data.pre_pc+1, vma=1, rw=1, ba=0)
        self.assert_cycle_signals(m, 2, vma=0, ba=0)
        ret_addr_lo = self.assert_cycle_signals(
            m, 3, address=self.data.pre_sp, vma=1, rw=0, ba=0)
        ret_addr_hi = self.assert_cycle_signals(
            m, 4, address=self.data.pre_sp-1, vma=1, rw=0, ba=0)
        self.assert_cycle_signals(m, 5, vma=0, ba=0)
        self.assert_cycle_signals(m, 6, vma=0, ba=0)
        self.assert_cycle_signals(m, 7, vma=0, ba=0)
        m.d.comb += offset.eq(data)

        m.d.comb += Assert(LCat(ret_addr_hi, ret_addr_lo) == ret_addr)
        self.assert_registers(m, PC=ret_addr + offset, SP=self.data.pre_sp-2)
        self.assert_flags(m)
