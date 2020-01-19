# verification.py: Formal verification framework for the 6800 CPU.
# Copyright (C) 2019 Robert Baruch <robert.c.baruch@gmail.com>
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

from typing import List, Optional, Type

from nmigen import Signal, Value, Module, Cat, Array, unsigned, Mux
from nmigen.asserts import Assert
from nmigen.hdl.ast import Statement
from nmigen.hdl.rec import Record, Layout
from consts.consts import Flags


def LCat(*args) -> Value:
    """Left or logical concatenation.

    Concatenates arguments such that the first argument is placed in the
    highest bit positions, and the last is placed in the lowest bit positions.
    """
    return Cat(*args[::-1])


class CycleSignals(Record):
    def __init__(self, name: str = None):
        super().__init__(Layout([
            ("address", unsigned(16)),
            ("data_in", unsigned(8)),
            ("data_out", unsigned(8)),
            ("rw", unsigned(1)),
            ("vma", unsigned(1)),
            ("ba", unsigned(1)),
            ("nmi", unsigned(1)),
            ("irq", unsigned(1)),
        ]), name=name)


class Verification(object):
    def __init__(self):
        self.want_cycles = Signal(4, name="want_cycles")
        self.want_a = Signal(8, name="want_a")
        self.want_b = Signal(8, name="want_b")
        self.want_x = Signal(16, name="want_x")
        self.want_sp = Signal(16, name="want_sp")
        self.want_pc = Signal(16, name="want_pc")
        self.want_flags = Signal(8, name="want_flags")
        self.want_signals = Array([CycleSignals(name=f"want_{i}_")
                                   for i in range(16)])

    def valid(self, instr: Value) -> Value:
        pass

    def verify(self, m: Module, instr: Value, data: 'FormalData'):
        self.data = data
        self.instr = instr
        self.check(m)

    def check(self, m: Module):
        pass

    def assert_cycles(self, m: Module, cycles: int):
        m.d.comb += self.want_cycles.eq(cycles)
        m.d.comb += Assert(self.data.cycle == self.want_cycles)

    def assert_cycle_signals(self, m: Module, cycle: int, vma: int, ba: int,
                             address: Value = None, rw: int = 0) -> Value:
        """Asserts that the signals for the given cycle number are as they are expected to be.

        Returns the data read or written, which is only valid if a read or write took place.

        Note that asserting for cycle 0 is pointless, since by definition the address will be
        the PC, data in will be the instruction, RW will be 1, VMA will be 1, and BA will be 0.

        *Generally*, for 2-cycle INHERENT instructions, there is no point in asserting for cycle 1,
        since that will always be the next instruction, which is irrelevant to the instruction
        being verified, except for the address lines, which will always be post_pc by definition.
        """
        want = self.want_signals[cycle]
        got = self.data.cycle_records[cycle]

        # We assign the arguments to signals so that they will appear in traces.
        m.d.comb += [
            want.ba.eq(ba),
            want.vma.eq(vma),
            Assert(want.ba == got.ba),
            Assert(want.vma == got.vma),
        ]
        if vma == 1:
            m.d.comb += [
                want.rw.eq(rw),
                want.address.eq(address),
                Assert(want.rw == got.rw),
                Assert(want.address == got.address),
            ]
            return got.data_in if rw == 1 else got.data_out
        return None

    def assert_registers(self, m: Module, A=None, B: Value = None,
                         X: Value = None, SP: Value = None, PC: Value = None):
        if A is not None:
            m.d.comb += self.want_a.eq(A[:8])
        else:
            m.d.comb += self.want_a.eq(self.data.pre_a)
        if B is not None:
            m.d.comb += self.want_b.eq(B[:8])
        else:
            m.d.comb += self.want_b.eq(self.data.pre_b)
        if X is not None:
            m.d.comb += self.want_x.eq(X[:16])
        else:
            m.d.comb += self.want_x.eq(self.data.pre_x)
        if SP is not None:
            m.d.comb += self.want_sp.eq(SP[:16])
        else:
            m.d.comb += self.want_sp.eq(self.data.pre_sp)
        if PC is not None:
            m.d.comb += self.want_pc.eq(PC[:16])
        else:
            m.d.comb += self.want_pc.eq(self.data.pre_pc)

        m.d.comb += Assert(self.data.post_a == self.want_a)
        m.d.comb += Assert(self.data.post_b == self.want_b)
        m.d.comb += Assert(self.data.post_x == self.want_x)
        m.d.comb += Assert(self.data.post_sp == self.want_sp)
        m.d.comb += Assert(self.data.post_pc == self.want_pc)

    def assert_flags(self,
                     m: Module,
                     H: Value = None,
                     I: Value = None,
                     N: Value = None,
                     Z: Value = None,
                     V: Value = None,
                     C: Value = None):
        expectedFlags = Signal(8)
        m.d.comb += expectedFlags.eq(self.flags(self.data.pre_ccs,
                                                H, I, N, Z, V, C))
        m.d.comb += [
            Assert(self.data.post_ccs[7] == expectedFlags[7]),
            Assert(self.data.post_ccs[6] == expectedFlags[6]),
            Assert(self.data.post_ccs[Flags.H] == expectedFlags[Flags.H]),
            Assert(self.data.post_ccs[Flags.I] == expectedFlags[Flags.I]),
            Assert(self.data.post_ccs[Flags.N] == expectedFlags[Flags.N]),
            Assert(self.data.post_ccs[Flags.Z] == expectedFlags[Flags.Z]),
            Assert(self.data.post_ccs[Flags.V] == expectedFlags[Flags.V]),
            Assert(self.data.post_ccs[Flags.C] == expectedFlags[Flags.C]),
        ]

    def flags(self,
              prev: Value,
              H: Value = None,
              I: Value = None,
              N: Value = None,
              Z: Value = None,
              V: Value = None,
              C: Value = None) -> Value:
        if H is None:
            H = prev[Flags.H]
        if I is None:
            I = prev[Flags.I]
        if N is None:
            N = prev[Flags.N]
        if Z is None:
            Z = prev[Flags.Z]
        if V is None:
            V = prev[Flags.V]
        if C is None:
            C = prev[Flags.C]
        return Cat(C, V, Z, N, I, H, 1, 1)


class FormalData(object):
    def __init__(self, verification: Optional[Verification]):
        self.verification = verification
        if verification is None:
            return

        self.snapshot_taken = Signal()

        self.instr = Signal(8)

        self.pre_ccs = Signal(8)
        self.pre_a = Signal(8)
        self.pre_b = Signal(8)
        self.pre_x = Signal(16)
        self.pre_sp = Signal(16)
        self.pre_pc = Signal(16)

        self.post_ccs = Signal(8)
        self.post_a = Signal(8)
        self.post_b = Signal(8)
        self.post_x = Signal(16)
        self.post_sp = Signal(16)
        self.post_pc = Signal(16)

        self.max_cycles = 16
        self.cycle = Signal(range(self.max_cycles), name="record_cycle")
        self.cycle_records = Array([CycleSignals(name=f"record{i}")
                                    for i in range(self.max_cycles)])

    def snapshot_signals(self, m: Module, addr: Value, din: Value, dout: Value,
                         rw: Value, vma: Value, ba: Value, irq: Value, nmi: Value) -> List[Statement]:
        s = self.cycle_records[self.cycle]
        return [
            s.address.eq(addr),
            s.data_in.eq(din),
            s.data_out.eq(dout),
            s.rw.eq(rw),
            s.vma.eq(vma),
            s.ba.eq(ba),
            s.irq.eq(irq),
            s.nmi.eq(nmi),
            self.cycle.eq(self.cycle + 1),
        ]

    def preSnapshot(self, m: Module, instr: Value, ccs: Value, a: Value, b: Value, x: Value, sp: Value, pc: Value) -> List[Statement]:
        return [
            self.snapshot_taken.eq(1),
            self.instr.eq(instr),
            self.pre_ccs.eq(ccs),
            self.pre_a.eq(a),
            self.pre_b.eq(b),
            self.pre_x.eq(x),
            self.pre_sp.eq(sp),
            self.pre_pc.eq(pc),
            self.cycle.eq(1),
        ]

    def noSnapshot(self, m: Module) -> Statement:
        return self.snapshot_taken.eq(0)

    def postSnapshot(self, m: Module, ccs: Value, a: Value, b: Value, x: Value, sp: Value, pc: Value) -> List[Statement]:
        return [
            self.post_ccs.eq(ccs),
            self.post_a.eq(a),
            self.post_b.eq(b),
            self.post_x.eq(x),
            self.post_sp.eq(sp),
            self.post_pc.eq(pc),
        ]
