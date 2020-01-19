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

from nmigen import Signal, Value, Cat, Module, Mux, Array
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Assume
from .verification import FormalData, Verification
from consts.consts import Flags


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("00011001")

    def check(self, m: Module):
        self.assert_cycles(m, 2)
        input1 = self.data.pre_a
        pre_h = self.data.pre_ccs[Flags.H]
        pre_c = self.data.pre_ccs[Flags.C]
        lo = input1[:4]
        hi = input1[4:]

        with m.If(pre_h):
            m.d.comb += Assume(lo <= 3)
            with m.If(pre_c):
                m.d.comb += Assume(hi <= 3)

        # Conditions taken directly from Motorola 6800 Programming Reference Manual,
        # the DAA instruction operation table.

        # Conditions are: C before DAA, a condition on hi, H before DAA, a condition on lo.
        conds = Array(
            [
                Array([0, hi <= 9, 0, lo <= 9]),
                Array([0, hi <= 8, 0, lo >= 10]),
                Array([0, hi <= 9, 1, lo <= 3]),
                Array([0, hi >= 10, 0, lo <= 9]),
                Array([0, hi >= 9, 0, lo >= 10]),
                Array([0, hi >= 10, 1, lo <= 3]),
                Array([1, hi <= 2, 0, lo <= 9]),
                Array([1, hi <= 2, 0, lo >= 10]),
                Array([1, hi <= 3, 1, lo <= 3]),
            ]
        )

        # Results are: DAA adjustment, state of C after DAA
        results = Array(
            [
                Array([0, 0]),
                Array([6, 0]),
                Array([6, 0]),
                Array([0x60, 1]),
                Array([0x66, 1]),
                Array([0x66, 1]),
                Array([0x60, 1]),
                Array([0x66, 1]),
                Array([0x66, 1]),
            ]
        )

        input_is_valid = Signal()
        expected_output = Signal(8)
        expected_c = Signal()

        for i in range(len(conds)):
            with m.If(
                (pre_c == conds[i][0])
                & conds[i][1]
                & (pre_h == conds[i][2])
                & conds[i][3]
            ):
                m.d.comb += input_is_valid.eq(1)
                m.d.comb += expected_output.eq(input1 + results[i][0])
                m.d.comb += expected_c.eq(results[i][1])

        z = expected_output == 0
        n = expected_output[7]

        with m.If(input_is_valid):
            self.assert_registers(m, A=expected_output, PC=self.data.pre_pc + 1)
            self.assert_flags(m, Z=z, N=n, C=expected_c)
