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

# To synthesize:
# python3 cpu_lattice_ice40hx8k.py

import os
import subprocess
import itertools
from typing import List

from core import Core

from nmigen import Signal, Module, Elaboratable, ClockDomain
from nmigen.build import Resource, ResourceError, Pins, Attrs, Connector, Clock
from nmigen.vendor.lattice_ice40 import LatticeICE40Platform

# Set FAKEMEM to True if you want to use a "software" ROM.
# This also hooks up the LEDs to the low byte of the address bus.
FAKEMEM = False

# This is the software ROM:
mem = {
    0xFFFE: 0x12,
    0xFFFF: 0x34,
    0x1234: 0x7E,  # JMP 0x1234
    0x1235: 0x12,
    0x1236: 0x34,
}

# Set SLOWCLK to True if you want a 1Hz clock.
SLOWCLK = False


class N6800(Elaboratable):
    def elaborate(self, platform):
        m = Module()

        cpu = Core()
        m.submodules += cpu
        m.domains.ph1 = ph1 = ClockDomain("ph1")
        m.domains.ph2 = ph2 = ClockDomain("ph2", clk_edge="neg")

        # Hook up clocks and reset to pins

        if not SLOWCLK:
            clk1 = platform.request("clk1")
            clk2 = platform.request("clk2")
            rst = platform.request("rst")
            m.d.comb += [
                ph1.rst.eq(rst.i),
                ph2.rst.eq(rst.i),
                ph1.clk.eq(clk1.i),
                ph2.clk.eq(clk2.i),
            ]

        if SLOWCLK:
            clk_freq = platform.default_clk_frequency
            timer = Signal(range(0, int(clk_freq // 2)),
                           reset=int(clk_freq // 2) - 1)
            tick = Signal()
            sync = ClockDomain()

            with m.If(timer == 0):
                m.d.sync += timer.eq(timer.reset)
                m.d.sync += tick.eq(~tick)
            with m.Else():
                m.d.sync += timer.eq(timer - 1)
            m.d.comb += [
                ph1.rst.eq(sync.rst),
                ph2.rst.eq(sync.rst),
                ph1.clk.eq(tick),
                ph2.clk.eq(~tick),
            ]

        # Hook up address lines to pins
        for i in range(16):
            pin = platform.request("addr", i)
            m.d.comb += pin.o.eq(cpu.Addr[i])

        if not FAKEMEM:
            # Hook up data in/out + direction to pins
            for i in range(8):
                pin = platform.request("data", i)
                m.d.comb += pin.o.eq(cpu.Dout[i])
                m.d.ph2 += cpu.Din[i].eq(pin.i)
                m.d.comb += pin.oe.eq(~cpu.RW)

        if FAKEMEM:
            with m.Switch(cpu.Addr):
                for addr, data in mem.items():
                    with m.Case(addr):
                        m.d.comb += cpu.Din.eq(data)
                with m.Default():
                    m.d.comb += cpu.Din.eq(0xFF)
            for i in range(8):
                pin = platform.request("led", i)
                m.d.comb += pin.o.eq(cpu.Addr[i])

        for i in range(2):
            pin = platform.request("reset_state", i)
            m.d.comb += pin.o.eq(cpu.reset_state[i])

        rw = platform.request("rw")
        m.d.comb += rw.o.eq(cpu.RW)

        return m


def Bus(*args, pins, invert=False, conn=None, attrs=None, default_name, dir):
    """Adds a bus resource. Add to resources using *Bus(...)."""
    assert isinstance(pins, (str, list, dict))

    if isinstance(pins, str):
        pins = pins.split()
    if isinstance(pins, list):
        pins = dict(enumerate(pins))

    resources = []
    for number, pin in pins.items():
        ios = [Pins(pin, dir=dir, invert=invert, conn=conn)]
        if attrs is not None:
            ios.append(attrs)
        resources.append(Resource.family(
            *args, number, default_name=default_name, ios=ios))
    return resources


class ICE40HX8KBEVNPlatform(LatticeICE40Platform):
    device = "iCE40HX8K"
    package = "CT256"

    # Resets should be on GBIN0/2/4/6. Clocks may be on any GBIN.
    resources: List[Resource] = [
        Resource("clk1", 0, Pins("J3", dir="i"), Clock(12e6),
                 Attrs(GLOBAL=True, IO_STANDARD="SB_LVCMOS")),  # GBIN6
        Resource("clk2", 0, Pins("G1", dir="i"), Clock(12e6),
                 Attrs(GLOBAL=True, IO_STANDARD="SB_LVCMOS")),  # GBIN7
        Resource("rst", 0, Pins("K9", dir="i"),
                 Attrs(GLOBAL=True, IO_STANDARD="SB_LVCMOS")),  # GBIN4
        *Bus(default_name="addr", pins="B1 B2 C1 C2 D1 D2 E2 F1 F2 G2 H1 H2 J2 J1 K3 K1",
             dir="o", attrs=Attrs(IO_STANDARD="SB_LVCMOS")),
        *Bus(default_name="data", pins="M3 L5 N3 P1 M4 P2 M5 R1",
             dir="io", attrs=Attrs(IO_STANDARD="SB_LVCMOS")),
        *Bus(default_name="led", pins="C3 B3 C4 C5 A1 A2 B4 B5",
             dir="o", attrs=Attrs(IO_STANDARD="SB_LVCMOS")),
        *Bus(default_name="reset_state", pins="L3 L1",
             dir="o", attrs=Attrs(IO_STANDARD="SB_LVCMOS")),
        Resource("rw", 0, Pins("E4", dir="o"), Attrs(IO_STANDARD="SB_LVCMOS")),
    ]

    default_clk = "clk1"
    default_rst = "rst"

    connectors: List[Connector] = []

    def toolchain_program(self, products, name):
        iceprog = os.environ.get("ICEPROG", "iceprog")
        with products.extract("{}.bin".format(name)) as bitstream_filename:
            subprocess.check_call([iceprog, "-S", bitstream_filename])


if __name__ == "__main__":
    ICE40HX8KBEVNPlatform().build(N6800(), do_program=False)
