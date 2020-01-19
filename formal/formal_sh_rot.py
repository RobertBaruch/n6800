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
from .verification import FormalData
from .alu_verification import Alu2Verification
from consts.consts import Flags


def Downto(v: Value, top: int, bottom: int) -> Value:
    """Inclusive slicing.

    Returns an equivalent nMigen 
    """
    if bottom > top:
        raise IndexError(
            f"Downto top must be greater than or equal to bottom: {top}, {bottom}"
        )
    return v[bottom : top + 1]


ROL = "01--1001"
ROR = "01--0110"
ASL = "01--1000"
ASR = "01--0111"
LSR = "01--0100"


class Formal(Alu2Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(ROL, ROR, ASL, ASR, LSR)

    def check(self, m: Module):
        input, actual_output = self.common_check(m)
        expected_output = Signal(8)
        pre_c = self.data.pre_ccs[Flags.C]
        c = Signal()

        with m.If(self.instr.matches(ROL)):
            # input[7..0], c ->
            # c, output[7..0]
            m.d.comb += [
                c.eq(input[7]),
                expected_output[0].eq(pre_c),
                Downto(expected_output, 7, 1).eq(Downto(input, 6, 0)),
            ]
        with m.Elif(self.instr.matches(ROR)):
            # c, input[7..0] ->
            # output[7..0], c
            m.d.comb += [
                c.eq(input[0]),
                expected_output[7].eq(pre_c),
                Downto(expected_output, 6, 0).eq(Downto(input, 7, 1)),
            ]
        with m.Elif(self.instr.matches(ASL)):
            # input[7..0], 0 ->
            # c, output[7..0]
            m.d.comb += [
                c.eq(input[7]),
                expected_output[0].eq(0),
                Downto(expected_output, 7, 1).eq(Downto(input, 6, 0)),
            ]
        with m.Elif(self.instr.matches(ASR)):
            # input[7], input[7..0] ->
            # output[7..0], c
            m.d.comb += [
                c.eq(input[0]),
                expected_output[7].eq(input[7]),
                Downto(expected_output, 6, 0).eq(Downto(input, 7, 1)),
            ]
        with m.Elif(self.instr.matches(LSR)):
            # 0, input[7..0] ->
            # output[7..0], c
            m.d.comb += [
                c.eq(input[0]),
                expected_output[7].eq(0),
                Downto(expected_output, 6, 0).eq(Downto(input, 7, 1)),
            ]

        m.d.comb += Assert(expected_output == actual_output)
        n = expected_output[7]
        z = expected_output == 0
        v = n ^ c
        self.assert_flags(m, Z=z, N=n, V=v, C=c)
