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
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("00011001")

    def check(self, m: Module, instr: Value, data: FormalData):
        input1 = data.pre_a
        pre_h = data.pre_ccs[Flags.H]
        pre_c = data.pre_ccs[Flags.C]
        post_c = data.post_ccs[Flags.C]
        lo = input1[:4]
        hi = input1[4:]
        out = data.post_a

        with m.If(pre_h):
            m.d.comb += Assume(lo <= 3)
            with m.If(pre_c):
                m.d.comb += Assume(hi <= 3)

        m.d.comb += [
            Assert(data.post_b == data.pre_b),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_read == 0),
            Assert(data.addresses_written == 0),
        ]
        m.d.comb += Assert(data.post_pc == data.plus16(data.pre_pc, 1)),

        # Conditions taken directly from Motorola 6800 Programming Reference Manual,
        # the DAA instruction operation table.

        # Conditions are: C before DAA, a condition on hi, H before DAA, a condition on lo.
        conds = Array([
            Array([0, hi <= 9, 0, lo <= 9]),
            Array([0, hi <= 8, 0, lo >= 10]),
            Array([0, hi <= 9, 1, lo <= 3]),
            Array([0, hi >= 10, 0, lo <= 9]),
            Array([0, hi >= 9, 0, lo >= 10]),
            Array([0, hi >= 10, 1, lo <= 3]),
            Array([1, hi <= 2, 0, lo <= 9]),
            Array([1, hi <= 2, 0, lo >= 10]),
            Array([1, hi <= 3, 1, lo <= 3]),
        ])

        # Results are: DAA adjustment, state of C after DAA
        results = Array([
            Array([0, 0]),
            Array([6, 0]),
            Array([6, 0]),
            Array([0x60, 1]),
            Array([0x66, 1]),
            Array([0x66, 1]),
            Array([0x60, 1]),
            Array([0x66, 1]),
            Array([0x66, 1]),
        ])

        for i in range(len(conds)):
            with m.If((pre_c == conds[i][0]) & conds[i][1] & (pre_h == conds[i][2]) & conds[i][3]):
                m.d.comb += Assert((out == (input1 +
                                            results[i][0])[:8]) & (post_c == results[i][1]))

        z = (out == 0)
        n = out[7]
        c = post_c

        self.assertFlags(m, data.post_ccs, data.pre_ccs,
                         Z=z, N=n, C=c)
