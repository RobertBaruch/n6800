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
        return instr.matches("1-011111", "1-1-1111")

    def check(self, m: Module, instr: Value, data: FormalData):
        mode = instr[4:6]
        use_sp = (instr[6] == 0)
        input = Mux(use_sp, data.pre_sp, data.pre_x)
        write_addr = Signal(16)

        m.d.comb += [
            Assert(data.post_a == data.pre_a),
            Assert(data.post_b == data.pre_b),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
        ]
        m.d.comb += [
            Assert(data.addresses_written == 2),
            Assert(data.write_addr[0] == write_addr),
            Assert(data.write_addr[1] == (write_addr + 1)[:16]),
            Assert(input == LCat(data.write_data[0], data.write_data[1])),
        ]

        with m.If(mode == ModeBits.DIRECT):
            m.d.comb += [
                Assert(data.addresses_read == 1),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                write_addr.eq(data.read_data[0]),
                Assert(data.post_pc == (data.pre_pc + 2)[:16]),
            ]

        with m.Elif(mode == ModeBits.EXTENDED):
            m.d.comb += [
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                Assert(data.read_addr[1] == (data.pre_pc + 2)[:16]),
                write_addr.eq(LCat(data.read_data[0], data.read_data[1])),
                Assert(data.post_pc == (data.pre_pc + 3)[:16]),
            ]

        with m.Elif(mode == ModeBits.INDEXED):
            m.d.comb += [
                Assert(data.addresses_read == 1),
                Assert(data.read_addr[0] == (data.pre_pc + 1)[:16]),
                write_addr.eq((data.pre_x + data.read_data[0])[:16]),
                Assert(data.post_pc == (data.pre_pc + 2)[:16]),
            ]

        z = (input == 0)
        n = input[15]
        self.assertFlags(m, data.post_ccs, data.pre_ccs, V=0, Z=z, N=n)
