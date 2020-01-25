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

JSR_IND = "10101101"
JSR_EXT = "10111101"


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(JSR_IND, JSR_EXT)

    def check(self, m: Module):
        with m.If(self.instr.matches(JSR_EXT)):
            self.assert_cycles(m, 9)
            addr_hi = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
            )
            addr_lo = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc + 2, vma=1, rw=1, ba=0
            )
            _ = self.assert_cycle_signals(
                m, 3, address=LCat(addr_hi, addr_lo), vma=1, rw=1, ba=0
            )
            retaddr_lo = self.assert_cycle_signals(
                m, 4, address=self.data.pre_sp, vma=1, rw=0, ba=0
            )
            retaddr_hi = self.assert_cycle_signals(
                m, 5, address=self.data.pre_sp - 1, vma=1, rw=0, ba=0
            )
            self.assert_cycle_signals(m, 6, vma=0, ba=0)
            self.assert_cycle_signals(m, 7, vma=0, ba=0)

            # I am not convinced the datasheet is correct for this cycle.
            # It claims there is a read of the pc+2 here.
            self.assert_cycle_signals(m, 8, vma=0, ba=0)

            self.assert_registers(
                m, SP=self.data.pre_sp - 2, PC=LCat(addr_hi, addr_lo))
            m.d.comb += Assert(
                LCat(retaddr_hi, retaddr_lo) == (self.data.pre_pc + 3)[:16]
            )

        with m.Else():
            self.assert_cycles(m, 8)
            offset = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
            )
            self.assert_cycle_signals(m, 2, vma=0, ba=0)
            retaddr_lo = self.assert_cycle_signals(
                m, 3, address=self.data.pre_sp, vma=1, rw=0, ba=0
            )
            retaddr_hi = self.assert_cycle_signals(
                m, 4, address=self.data.pre_sp - 1, vma=1, rw=0, ba=0
            )
            self.assert_cycle_signals(m, 5, vma=0, ba=0)
            self.assert_cycle_signals(m, 6, vma=0, ba=0)
            self.assert_cycle_signals(m, 7, vma=0, ba=0)

            self.assert_registers(
                m, SP=self.data.pre_sp - 2, PC=self.data.pre_x + offset
            )
            m.d.comb += Assert(
                LCat(retaddr_hi, retaddr_lo) == (self.data.pre_pc + 2)[:16]
            )

        self.assert_flags(m)
