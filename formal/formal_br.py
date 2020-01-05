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
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("0010----")

    def check(self, m: Module, instr: Value, data: FormalData):
        m.d.comb += [
            Assert(data.post_ccs == data.pre_ccs),
            Assert(data.post_a == data.pre_a),
            Assert(data.post_b == data.pre_b),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_written == 0),
        ]

        m.d.comb += [
            Assert(data.addresses_read == 1),
            Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
        ]

        n = data.pre_ccs[Flags.N]
        z = data.pre_ccs[Flags.Z]
        v = data.pre_ccs[Flags.V]
        c = data.pre_ccs[Flags.C]
        offset = Signal(signed(8))
        br = instr[:4]

        take_branch = Array([
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
        ])
        m.d.comb += offset.eq(data.read_data[0])
        m.d.comb += Assert(data.post_pc == Mux(
            take_branch[br], (data.pre_pc + 2 + offset)[:16], (data.pre_pc + 2)[:16]))
