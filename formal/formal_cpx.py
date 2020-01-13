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
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("10--1100")

    def check(self, m: Module, instr: Value, data: FormalData):
        mode = instr[4:6]
        read_addr = Signal(16)
        read_data = Signal(16)

        m.d.comb += [
            Assert(data.post_a == data.pre_a),
            Assert(data.post_b == data.pre_b),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
        ]

        with m.If(mode == ModeBits.DIRECT):
            m.d.comb += [
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                read_addr.eq(data.read_data[0]),
                Assert(data.read_addr[1] == read_addr),
                Assert(data.read_addr[2] == (read_addr + 1)[:16]),
                read_data.eq(LCat(data.read_data[1], data.read_data[2])),
                Assert(data.post_pc == (data.pre_pc + 2)[:16]),
            ]

        with m.Elif(mode == ModeBits.EXTENDED):
            m.d.comb += [
                Assert(data.addresses_read == 4),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                Assert(data.read_addr[1] == (data.pre_pc + 2)[:16]),
                read_addr.eq(LCat(data.read_data[0], data.read_data[1])),
                Assert(data.read_addr[2] == read_addr),
                Assert(data.read_addr[3] == (read_addr + 1)[:16]),
                read_data.eq(LCat(data.read_data[2], data.read_data[3])),
                Assert(data.post_pc == (data.pre_pc + 3)[:16]),
            ]

        with m.Elif(mode == ModeBits.IMMEDIATE):
            m.d.comb += [
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                Assert(data.read_addr[1] == (data.pre_pc + 2)[:16]),
                read_data.eq(LCat(data.read_data[0], data.read_data[1])),
                Assert(data.post_pc == (data.pre_pc + 3)[:16]),
            ]

        with m.Else():
            m.d.comb += [
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                read_addr.eq((data.pre_x + data.read_data[0])[:16]),
                Assert(data.read_addr[1] == read_addr),
                Assert(data.read_addr[2] == (read_addr + 1)[:16]),
                read_data.eq(LCat(data.read_data[1], data.read_data[2])),
                Assert(data.post_pc == (data.pre_pc + 2)[:16]),
            ]

        sub = data.pre_x[8:] - read_data[8:]
        z = (read_data == data.pre_x)
        n = sub[7]
        v = (data.pre_x[15] & ~read_data[15] & ~n) | (
            ~data.pre_x[15] & read_data[15] & n)
        self.assertFlags(m, data.post_ccs, data.pre_ccs, V=v, Z=z, N=n)
