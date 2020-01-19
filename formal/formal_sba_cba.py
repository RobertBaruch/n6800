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


SBA = "00010000"
CBA = "00010001"


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(SBA, CBA)

    def check(self, m: Module):
        self.assert_cycles(m, 2)

        input1 = self.data.pre_a
        input2 = self.data.pre_b
        carry_in = Signal()
        sum9 = Signal(9)
        sum8 = Signal(8)

        n = sum9[7]
        c = ~sum9[8]
        z = (sum9[:8] == 0)
        v = (sum8[7] ^ sum9[8])

        m.d.comb += carry_in.eq(0)

        m.d.comb += [
            sum9.eq(input1 + ~input2 + ~carry_in),
            sum8.eq(input1[:7] + ~input2[:7] + ~carry_in),
        ]
        with m.If(self.instr.matches(SBA)):
            self.assert_registers(m, A=sum9, PC=self.data.pre_pc+1)
        with m.Else():
            self.assert_registers(m, PC=self.data.pre_pc+1)

        self.assert_flags(m, Z=z, N=n, V=v, C=c)
