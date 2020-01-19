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
        return instr.matches("00111111")

    def check(self, m: Module):
        self.assert_cycles(m, 12)
        self.assert_cycle_signals(m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0)
        ret_addr_lo = self.assert_cycle_signals(
            m, 2, address=self.data.pre_sp, vma=1, rw=0, ba=0
        )
        ret_addr_hi = self.assert_cycle_signals(
            m, 3, address=self.data.pre_sp - 1, vma=1, rw=0, ba=0
        )
        x_lo = self.assert_cycle_signals(
            m, 4, address=self.data.pre_sp - 2, vma=1, rw=0, ba=0
        )
        x_hi = self.assert_cycle_signals(
            m, 5, address=self.data.pre_sp - 3, vma=1, rw=0, ba=0
        )
        a = self.assert_cycle_signals(
            m, 6, address=self.data.pre_sp - 4, vma=1, rw=0, ba=0
        )
        b = self.assert_cycle_signals(
            m, 7, address=self.data.pre_sp - 5, vma=1, rw=0, ba=0
        )
        ccs = self.assert_cycle_signals(
            m, 8, address=self.data.pre_sp - 6, vma=1, rw=0, ba=0
        )
        self.assert_cycle_signals(m, 9, vma=0, ba=0)
        target_hi = self.assert_cycle_signals(m, 10, address=0xFFFA, vma=1, rw=1, ba=0)
        target_lo = self.assert_cycle_signals(m, 11, address=0xFFFB, vma=1, rw=1, ba=0)

        m.d.comb += [
            Assert(LCat(ret_addr_hi, ret_addr_lo) == (self.data.pre_pc + 1)[:16]),
            Assert(LCat(x_hi, x_lo) == self.data.pre_x),
            Assert(a == self.data.pre_a),
            Assert(b == self.data.pre_b),
            Assert(ccs == self.data.pre_ccs),
        ]

        self.assert_registers(m, PC=LCat(target_hi, target_lo), SP=self.data.pre_sp - 7)
        self.assert_flags(m, I=1)
