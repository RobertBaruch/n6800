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

from typing import Tuple

from nmigen import Signal, Value, Cat, Module, Mux, Const, unsigned
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification, CycleSignals, LCat
from consts.consts import ModeBits


class AluVerification(Verification):
    def __init__(self):
        super().__init__()

    def common_check(self, m: Module) -> Tuple[Value, Value, Value, Value, Value]:
        """Does common checks for ALU instructions.

        Returns a tuple of values: (input1, input2, actual_output, instruction size, use_a).
        The caller should use those values to verify flags and expected output.
        """
        mode = self.instr[4:6]
        b = self.instr[6]
        input1 = Mux(b, self.data.pre_b, self.data.pre_a)
        input2 = Signal(8)
        actual_output = Mux(b, self.data.post_b, self.data.post_a)
        size = Signal(3)

        with m.If(mode == ModeBits.DIRECT.value):
            self.assert_cycles(m, 3)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1, vma=1, ba=0
            )
            data = self.assert_cycle_signals(m, 2, address=addr_lo, rw=1, vma=1, ba=0)
            m.d.comb += input2.eq(data)
            m.d.comb += size.eq(2)

        with m.Elif(mode == ModeBits.EXTENDED.value):
            self.assert_cycles(m, 4)
            addr_hi = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1, vma=1, ba=0
            )
            addr_lo = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc + 2, rw=1, vma=1, ba=0
            )
            data = self.assert_cycle_signals(
                m, 3, address=LCat(addr_hi, addr_lo), rw=1, vma=1, ba=0
            )
            m.d.comb += input2.eq(data)
            m.d.comb += size.eq(3)

        with m.Elif(mode == ModeBits.IMMEDIATE.value):
            self.assert_cycles(m, 3)
            data = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1, vma=1, ba=0
            )
            m.d.comb += input2.eq(data)
            m.d.comb += size.eq(2)

        with m.Elif(mode == ModeBits.INDEXED.value):
            self.assert_cycles(m, 5)
            offset = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1, vma=1, ba=0
            )
            self.assert_cycle_signals(m, 2, vma=0, ba=0)
            self.assert_cycle_signals(m, 3, vma=0, ba=0)
            data = self.assert_cycle_signals(
                m, 4, address=self.data.pre_x + offset, rw=1, vma=1, ba=0
            )
            m.d.comb += input2.eq(data)
            m.d.comb += size.eq(2)

        return (input1, input2, actual_output, size, ~b)


class Alu2Verification(Verification):
    def __init__(self):
        super().__init__()

    def common_check(self, m: Module, store: bool = True) -> Tuple[Value, Value]:
        """Does common checks for ALU instructions from 0x40 to 0x7F.

        Returns a tuple of values: (input, actual_output). The
        # caller should use those values to verify flags and expected output.
        """
        mode = self.instr[4:6]
        input = Signal(8)
        actual_output = Signal(8)
        size = Signal(3)

        with m.If(mode == ModeBits.A):
            self.assert_cycles(m, 2)
            m.d.comb += size.eq(1)
            m.d.comb += input.eq(self.data.pre_a)
            m.d.comb += actual_output.eq(self.data.post_a)
            self.assert_registers(m, A=actual_output, PC=self.data.pre_pc + size)

        with m.Elif(mode == ModeBits.B):
            self.assert_cycles(m, 2)
            m.d.comb += size.eq(1)
            m.d.comb += input.eq(self.data.pre_b)
            m.d.comb += actual_output.eq(self.data.post_b)
            self.assert_registers(m, B=actual_output, PC=self.data.pre_pc + size)

        with m.Elif(mode == ModeBits.EXTENDED.value):
            self.assert_cycles(m, 6)
            m.d.comb += size.eq(3)
            addr_hi = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1, vma=1, ba=0
            )
            addr_lo = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc + 2, rw=1, vma=1, ba=0
            )
            data = self.assert_cycle_signals(
                m, 3, address=LCat(addr_hi, addr_lo), rw=1, vma=1, ba=0
            )
            self.assert_cycle_signals(m, 4, vma=0, ba=0)
            m.d.comb += input.eq(data)

            if store:
                data = self.assert_cycle_signals(
                    m, 5, address=LCat(addr_hi, addr_lo), rw=0, vma=1, ba=0
                )
                m.d.comb += actual_output.eq(data)
            else:
                self.assert_cycle_signals(m, 5, vma=0, ba=0)

            self.assert_registers(m, PC=self.data.pre_pc + size)

        with m.Elif(mode == ModeBits.INDEXED.value):
            self.assert_cycles(m, 7)
            m.d.comb += size.eq(2)
            offset = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1, vma=1, ba=0
            )
            self.assert_cycle_signals(m, 2, vma=0, ba=0)
            self.assert_cycle_signals(m, 3, vma=0, ba=0)
            data = self.assert_cycle_signals(
                m, 4, address=self.data.pre_x + offset, rw=1, vma=1, ba=0
            )
            m.d.comb += input.eq(data)

            if store:
                self.assert_cycle_signals(m, 5, vma=0, ba=0)
                data = self.assert_cycle_signals(
                    m, 6, address=self.data.pre_x + offset, rw=0, vma=1, ba=0
                )
                m.d.comb += actual_output.eq(data)
            else:
                self.assert_cycle_signals(m, 6, vma=0, ba=0)

            self.assert_registers(m, PC=self.data.pre_pc + size)

        return (input, actual_output)
