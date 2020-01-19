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
from consts.consts import ModeBits, Flags


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("1---1110")

    def check(self, m: Module):
        mode = self.instr[4:6]
        use_sp = self.instr[6] == 0
        data = Signal(16)
        size = Signal(4)

        with m.If(mode == ModeBits.DIRECT):
            self.assert_cycles(m, 4)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
            )
            data_hi = self.assert_cycle_signals(
                m, 2, address=addr_lo, vma=1, rw=1, ba=0
            )
            data_lo = self.assert_cycle_signals(
                m, 3, address=addr_lo + 1, vma=1, rw=1, ba=0
            )
            m.d.comb += data.eq(LCat(data_hi, data_lo))
            m.d.comb += size.eq(2)

        with m.Elif(mode == ModeBits.EXTENDED):
            self.assert_cycles(m, 5)
            addr_hi = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
            )
            addr_lo = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc + 2, vma=1, rw=1, ba=0
            )
            data_hi = self.assert_cycle_signals(
                m, 3, address=LCat(addr_hi, addr_lo), vma=1, rw=1, ba=0
            )
            data_lo = self.assert_cycle_signals(
                m, 4, address=LCat(addr_hi, addr_lo) + 1, vma=1, rw=1, ba=0
            )
            m.d.comb += data.eq(LCat(data_hi, data_lo))
            m.d.comb += size.eq(3)

        with m.Elif(mode == ModeBits.IMMEDIATE):
            self.assert_cycles(m, 3)
            data_hi = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
            )
            data_lo = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc + 2, vma=1, rw=1, ba=0
            )
            m.d.comb += data.eq(LCat(data_hi, data_lo))
            m.d.comb += size.eq(3)

        with m.Else():
            self.assert_cycles(m, 6)
            offset = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
            )
            self.assert_cycle_signals(m, 2, vma=0, ba=0)
            self.assert_cycle_signals(m, 3, vma=0, ba=0)
            data_hi = self.assert_cycle_signals(
                m, 4, address=self.data.pre_x + offset, vma=1, rw=1, ba=0
            )
            data_lo = self.assert_cycle_signals(
                m, 5, address=self.data.pre_x + offset + 1, vma=1, rw=1, ba=0
            )
            m.d.comb += data.eq(LCat(data_hi, data_lo))
            m.d.comb += size.eq(2)

        z = data == 0
        n = data[15]
        with m.If(use_sp):
            self.assert_registers(m, SP=data, PC=self.data.pre_pc + size)
        with m.Else():
            self.assert_registers(m, X=data, PC=self.data.pre_pc + size)
        self.assert_flags(m, V=0, Z=z, N=n)
