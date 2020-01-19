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
from consts.consts import Flags


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("00000110")

    def check(self, m: Module):
        self.assert_cycles(m, 2)
        self.assert_registers(m, PC=self.data.pre_pc + 1)
        self.assert_flags(
            m,
            H=self.data.pre_a[Flags.H],
            I=self.data.pre_a[Flags.I],
            N=self.data.pre_a[Flags.N],
            Z=self.data.pre_a[Flags.Z],
            V=self.data.pre_a[Flags.V],
            C=self.data.pre_a[Flags.C],
        )
