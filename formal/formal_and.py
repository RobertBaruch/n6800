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

from nmigen import Signal, Value, Cat, Module, Mux, Const, unsigned
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from .alu_verification import AluVerification


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("1---0100")

    def check(self, m: Module):
        input1, input2, actual_output, size, use_a = self.common_check(m)
        output = input1 & input2

        z = output == 0
        n = output[7]
        v = 0

        with m.If(use_a):
            self.assert_registers(m, A=output, PC=self.data.pre_pc+size)
        with m.Else():
            self.assert_registers(m, B=output, PC=self.data.pre_pc+size)
        self.assert_flags(m, Z=z, N=n, V=v)
