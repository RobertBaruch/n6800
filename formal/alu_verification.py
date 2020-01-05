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
from .verification import FormalData, Verification
from consts.consts import ModeBits


class AluVerification(Verification):
    def __init__(self):
        pass

    def common_check(self, m: Module, instr: Value, data: FormalData) -> Tuple[Value, Value, Value]:
        """Does common checks for ALU instructions.

        Returns a tuple of values: (input1, input2, actual_output). The caller should use those
        values to verify flags and expected output.
        """
        mode = instr[4:6]
        b = instr[6]
        input1 = Mux(b, data.pre_b, data.pre_a)
        input2 = Signal(8)
        actual_output = Mux(b, data.post_b, data.post_a)

        with m.If(b):
            m.d.comb += Assert(data.post_a == data.pre_a)
        with m.Else():
            m.d.comb += Assert(data.post_b == data.pre_b)

        m.d.comb += [
            Assert(data.post_x == data.pre_x),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_written == 0),
        ]

        with m.If(mode == ModeBits.DIRECT.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.read_data[0]),
                input2.eq(data.read_data[1]),
            ]

        with m.Elif(mode == ModeBits.EXTENDED.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
                Assert(
                    data.read_addr[2] == Cat(data.read_data[1], data.read_data[0])),
                input2.eq(data.read_data[2]),
            ]

        with m.Elif(mode == ModeBits.IMMEDIATE.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 1),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                input2.eq(data.read_data[0]),
            ]

        with m.Elif(mode == ModeBits.INDEXED.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == (
                    data.pre_x + data.read_data[0])[:16]),
                input2.eq(data.read_data[1]),
            ]

        return (input1, input2, actual_output)
