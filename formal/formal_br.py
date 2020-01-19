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

from enum import IntEnum

from nmigen import Signal, Value, Cat, Module, signed, Mux, Const, Array
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from consts.consts import Flags


class Branch(IntEnum):
    """Encodings for the low 4 bits of branch instructions."""

    A = 0x0
    N = 0x1
    HI = 0x2
    LS = 0x3
    CC = 0x4
    CS = 0x5
    NE = 0x6
    EQ = 0x7
    VC = 0x8
    VS = 0x9
    PL = 0xA
    MI = 0xB
    GE = 0xC
    LT = 0xD
    GT = 0xE
    LE = 0xF


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("0010----")

    def check(self, m: Module):
        self.assert_cycles(m, 4)
        data = self.assert_cycle_signals(
            m, 1, address=self.data.pre_pc + 1, vma=1, rw=1, ba=0
        )
        self.assert_cycle_signals(m, 2, vma=0, ba=0)
        self.assert_cycle_signals(m, 3, vma=0, ba=0)

        n = self.data.pre_ccs[Flags.N]
        z = self.data.pre_ccs[Flags.Z]
        v = self.data.pre_ccs[Flags.V]
        c = self.data.pre_ccs[Flags.C]
        offset = Signal(signed(8))
        br = self.instr[:4]

        take_branch = Array(
            [
                Const(1),
                Const(0),
                (c | z) == 0,
                (c | z) == 1,
                c == 0,
                c == 1,
                z == 0,
                z == 1,
                v == 0,
                v == 1,
                n == 0,
                n == 1,
                (n ^ v) == 0,
                (n ^ v) == 1,
                (z | (n ^ v)) == 0,
                (z | (n ^ v)) == 1,
            ]
        )
        m.d.comb += offset.eq(data)
        target = Mux(
            take_branch[br], self.data.pre_pc + 2 + offset, self.data.pre_pc + 2
        )
        self.assert_registers(m, PC=target)
        self.assert_flags(m)
