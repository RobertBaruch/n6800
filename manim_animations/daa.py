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

from manimlib.imports import *
from manimlib.imports import Scene

# add_sub.py implements the storyboard storyboard_add_sub.pdf.
# Inkscape file of storyboard is the svg file.

# Install 3Blue1Brown's manim and prerequisites:
#
# (create a virtual environment for manim and activate it!)
# pip3 install manimlib
# sudo apt install ffmpeg sox texlive-full libcairo2-dev
#
# Run as:
#
# manim add_sub.py Shapes --high_quality # for 1080p60 output
# manim add_sub.py Shapes -l # for 480p15 output


class Shapes(Scene):
    def card(self):
        return Rectangle(height=self.H, width=self.W)

    def fadeout_all(self):
        self.play(*[FadeOut(x) for x in self.get_mobjects()])

    def do(self, i, f):
        f()
        print(f"{i}: There are {len(self.get_mobjects())} mobjects and {len(self.foreground_mobjects)} foreground mobjects in the scene left")
        self.wait(1)

    def construct(self):
        self.H = 0.8
        self.W = 0.5
        self.HSPACE = self.W * 1.3
        self.VSPACE = self.H * 1.4
        self.XPOS0 = 6*self.HSPACE*LEFT
        self.CARDSCALE = 1.3

        self.do(1, self.storyboard1)
        self.do(2, self.storyboard2)
        self.do(3, self.storyboard3)
        self.do(4, self.storyboard4)
        self.do(5, self.storyboard5)
        self.do(6, self.storyboard6)
        self.do(7, self.storyboard7)
        self.do(8, self.storyboard8)
        self.do(9, self.storyboard9)
        self.do(11, self.storyboard11)
        self.do(12, self.storyboard12)

    def storyboard1(self):
        text = TexMobject(r"\text{B}", r"\text{INARY}").scale(2)
        text2 = TexMobject(r"\text{C}", r"\text{ODED}").scale(2).shift(DOWN)
        text3 = TexMobject(r"\text{D}", r"\text{ECIMAL}").scale(
            2).shift(2*DOWN)
        for i, item in enumerate(text):
            text2[i].align_to(item, LEFT)
            text3[i].align_to(item, LEFT)
        self.texts = Group(text, text2, text3).center()
        self.play(FadeIn(self.texts))
        self.wait(1)
        self.play(*[FadeOut(x[1]) for x in self.texts])
        self.wait(1)

        self.bcd = Group(text[0], text2[0], text3[0])
        self.bcd[0].generate_target()
        self.bcd[0].target.scale(0.5).move_to(
            TOP + LEFT_SIDE, UL).shift(MED_SMALL_BUFF*DR)
        self.bcd[1].generate_target()
        self.bcd[1].target.scale(0.5).next_to(self.bcd[0].target)
        self.bcd[2].generate_target()
        self.bcd[2].target.scale(0.5).next_to(self.bcd[1].target)
        self.play(*[MoveToTarget(x) for x in self.bcd])
        self.wait(1)

    def storyboard2(self):
        self.rect_dec = self.card()
        self.eq = TexMobject(r"=").scale(2).next_to(self.rect_dec)
        self.rect_bin = [self.card() for i in range(4)]
        self.rect_bin[0].next_to(self.eq)
        for i in range(1, 4):
            self.rect_bin[i].next_to(self.rect_bin[i-1])
        group = Group(self.rect_dec, self.eq, *self.rect_bin).center()
        self.play(FadeIn(group))
        self.wait(1)

        self.dec = TexMobject(r"0").scale(
            self.CARDSCALE).move_to(self.rect_dec.get_center())
        self.bin_num = [TexMobject(r"0").scale(self.CARDSCALE).move_to(self.rect_bin[i])
                        for i in range(4)]
        self.play(FadeIn(self.dec), *
                  [FadeIn(self.bin_num[i]) for i in range(4)])
        self.wait(1)

        for n in range(1, 10):
            s = f"{n:04b}"
            s_prev = f"{n-1:04b}"
            dec2 = TexMobject(f"{n}").scale(
                self.CARDSCALE).move_to(self.rect_dec)

            anims = []
            bin2 = []
            for i in range(4):
                if s[i] != s_prev[i]:
                    bin2.append(TexMobject(s[i]).scale(
                        self.CARDSCALE).move_to(self.rect_bin[i]))
                    anims.append(FadeInFrom(bin2[i], DOWN))
                    anims.append(FadeOutAndShift(self.bin_num[i], UP))
                else:
                    bin2.append(self.bin_num[i])

            self.play(*anims, FadeInFrom(dec2, DOWN),
                      FadeOutAndShift(self.dec, UP), run_time=0.5)
            self.bin_num = bin2
            self.dec = dec2
        self.wait(1)

        s = f"{0:04b}"
        s_prev = f"{9:04b}"
        dec2 = TexMobject("0").scale(self.CARDSCALE).move_to(self.rect_dec)

        anims = []
        bin2 = []
        for i in range(4):
            if s[i] != s_prev[i]:
                bin2.append(TexMobject(s[i]).scale(
                    self.CARDSCALE).move_to(self.rect_bin[i]))
                anims.append(FadeInFrom(bin2[i], DOWN))
                anims.append(FadeOutAndShift(self.bin_num[i], UP))
            else:
                bin2.append(self.bin_num[i])

        self.carry1 = TexMobject("1").scale(
            0.7*self.CARDSCALE).next_to(self.rect_bin[0], UL)
        self.carry2 = TexMobject("1").scale(
            0.7*self.CARDSCALE).next_to(self.rect_dec, UL)

        self.play(*anims, FadeInFrom(dec2, DOWN),
                  FadeOutAndShift(self.dec, UP),
                  FadeIn(self.carry1), FadeIn(self.carry2))
        self.bin_num = bin2
        self.dec = dec2
        self.wait(1)
        self.play(*[FadeOut(x)
                    for x in [self.carry1, self.carry2, self.dec, *self.bin_num]])
        self.wait(1)

    def storyboard3(self):
        self.dec = TexMobject(r"9").scale(
            self.CARDSCALE).move_to(self.rect_dec.get_center())
        s = f"{9:04b}"
        self.bin_num = [TexMobject(s[i]).scale(self.CARDSCALE).move_to(self.rect_bin[i])
                        for i in range(4)]
        self.play(FadeIn(self.dec), *
                  [FadeIn(self.bin_num[i]) for i in range(4)])
        self.wait(1)

        s = f"{10:04b}"
        s_prev = f"{9:04b}"
        dec2 = TexMobject(r"\text{?}").set_color(COLOR_MAP["RED_C"]).scale(
            self.CARDSCALE).move_to(self.rect_dec)
        anims = []
        bin2 = []
        for i in range(4):
            if s[i] != s_prev[i]:
                bin2.append(TexMobject(s[i]).scale(
                    self.CARDSCALE).move_to(self.rect_bin[i]))
                anims.append(FadeInFrom(bin2[i], DOWN))
                anims.append(FadeOutAndShift(self.bin_num[i], UP))
            else:
                bin2.append(self.bin_num[i])
        self.play(*anims, FadeInFrom(dec2, DOWN),
                  FadeOutAndShift(self.dec, UP), run_time=0.5)
        self.dec = dec2
        self.bin_num = bin2
        self.wait(1)

    def storyboard4(self):
        self.text_daa = TexMobject(r"\text{DAA}").move_to(
            TOP + LEFT_SIDE, UL).shift(MED_SMALL_BUFF*DR)
        self.play(FadeOut(self.bcd), FadeIn(self.text_daa))
        self.wait(1)

        for n in range(11, 16):
            s = f"{n:04b}"
            s_prev = f"{n-1:04b}" if n > 11 else f"{10:04b}"
            dec2 = TexMobject(r"\text{?}").set_color(COLOR_MAP["RED_C"]).scale(
                self.CARDSCALE).move_to(self.rect_dec)

            anims = []
            bin2 = []
            for i in range(4):
                if s[i] != s_prev[i]:
                    bin2.append(TexMobject(s[i]).scale(
                        self.CARDSCALE).move_to(self.rect_bin[i]))
                    anims.append(FadeInFrom(bin2[i], DOWN))
                    anims.append(FadeOutAndShift(self.bin_num[i], UP))
                else:
                    bin2.append(self.bin_num[i])

            self.play(*anims, FadeInFrom(dec2, DOWN),
                      FadeOutAndShift(self.dec, UP), run_time=0.5)
            self.bin_num = bin2
            self.dec = dec2
        self.wait(1)

        s = f"{0:04b}"
        s_prev = f"{15:04b}"
        dec2 = TexMobject("0").scale(self.CARDSCALE).move_to(self.rect_dec)

        anims = []
        bin2 = []
        for i in range(4):
            if s[i] != s_prev[i]:
                bin2.append(TexMobject(s[i]).scale(
                    self.CARDSCALE).move_to(self.rect_bin[i]))
                anims.append(FadeInFrom(bin2[i], DOWN))
                anims.append(FadeOutAndShift(self.bin_num[i], UP))
            else:
                bin2.append(self.bin_num[i])

        self.play(*anims, FadeInFrom(dec2, DOWN),
                  FadeOutAndShift(self.dec, UP),
                  FadeIn(self.carry1), FadeIn(self.carry2))
        self.bin_num = bin2
        self.dec = dec2
        self.wait(1)

    def storyboard5(self):
        self.play(*[FadeOut(x) for x in [*self.bin_num, *self.rect_bin, self.dec,
                                         self.rect_dec, self.eq, self.carry1, self.carry2]])
        self.wait(1)

        t = []
        for i in range(1, 10):
            h = r"\phantom{^{1}}" + \
                f"{9+i:X}" if (9 + i < 0x10) else r"^{1}" + f"{9+i-0x10}"
            t.append(TexMobject(f"9+{i}", r"\,=\,",
                                f"{h}+6", r"\,=\,", r"^{1}" + f"{i-1}"))

        h = r"^{1}" + f"{1+9+9-0x10}"
        t.append(TexMobject(f"1+9+9", r"\,=\,",
                            f"{h}+6", r"\,=\,", r"^{1}9"))

        for eq in [t[i] for i in range(0, len(t)-1)]:
            for i, item in enumerate(eq):
                item.align_to(t[len(t)-1][i], RIGHT)

        for i in range(0, len(t)):
            t[i] = VGroup(*t[i])

        for i in range(1, len(t)):
            t[i].shift(i * 0.5 * DOWN)

        self.t = t
        self.all = VGroup(*self.t)
        self.all.center()

        self.play(*[Write(self.t[i]) for i in range(0, len(t)-1)])
        self.wait(1)

    def storyboard6(self):
        self.play(Write(self.t[-1]))
        self.wait(1)

    def storyboard7(self):
        self.play(*[FadeOut(x) for x in self.all])
        self.wait(1)

        self.low_add6 = TexMobject(
            "A-F", r",\,{}^{1}X", r"\,{}\implies{}\,", "+6").center()
        self.low_add6 = VGroup(*self.low_add6)
        self.play(FadeIn(self.low_add6[0]))
        self.wait(1)
        self.play(FadeIn(self.low_add6[1]), FadeIn(self.low_add6[2]))
        self.wait(1)

    def storyboard8(self):
        self.low_outline = Rectangle().surround(
            self.low_add6, buff=LARGE_BUFF, stretch=True)
        self.low_group = Group(self.low_outline, self.low_add6)
        self.play(FadeIn(self.low_outline))
        self.wait()

        self.high_add6 = TexMobject(
            "A-F", r",\,{}^{1}X", r"\,{}\implies{}\,", "+6").center()
        self.high_add6 = VGroup(*self.high_add6)
        self.high_outline = Rectangle().surround(
            self.high_add6, buff=LARGE_BUFF, stretch=True)
        self.high_group = Group(self.high_outline, self.high_add6)

        self.low_group.generate_target()
        self.low_group.target.next_to(self.high_group)

        self.all_group = Group(self.high_group, self.low_group.target).center()

        self.play(MoveToTarget(self.low_group))
        self.wait(1)

        self.play(FadeIn(self.high_group))
        self.wait(1)

    def storyboard9(self):
        self.play(ApplyMethod(self.low_add6[0].set_color, COLOR_MAP["RED_C"]))
        self.wait(1)

        self.new_high_add6 = TexMobject(
            "9,", "A-F", r",\,{}^{1}X", r"\,{}\implies{}\,", "+6").move_to(self.high_add6, RIGHT)
        self.new_high_add6 = VGroup(*self.new_high_add6)
        self.new_high_add6[0].set_color(COLOR_MAP["RED_C"])
        self.new_high_outline = Rectangle().surround(
            self.new_high_add6, buff=LARGE_BUFF, stretch=True)
        self.play(ApplyMethod(self.high_outline.stretch_to_fit_width,
                              self.new_high_outline.get_width(), {"about_edge": RIGHT}))
        self.play(FadeOut(self.high_add6), FadeIn(self.new_high_add6))
        self.wait(1)

    def storyboard11(self):
        self.daa_algo = Group(self.new_high_add6,
                              self.high_outline, self.low_group)
        self.daa_algo.generate_target()
        self.daa_algo.target.move_to(TOP, UP).shift(
            MED_SMALL_BUFF*DOWN).scale(0.85)

        self.play(FadeOut(self.text_daa),
                  MoveToTarget(self.daa_algo))
        self.wait(1)

        # 99 + 1

        decL = TexMobject(r"9").scale(
            self.CARDSCALE).move_to(TOP, UP).shift(2 * DOWN + LEFT)
        decH = TexMobject(r"9").scale(
            self.CARDSCALE).next_to(decL, LEFT)

        self.play(FadeIn(decL), FadeIn(decH))
        self.wait(1)

        addend = TexMobject(r"1").scale(
            self.CARDSCALE).next_to(decL, DOWN)
        plus = TexMobject(
            "+").scale(0.7 * self.CARDSCALE).next_to(decH, LEFT).shift(0.5*DOWN)
        end = addend.get_corner(
            DOWN+RIGHT) + 0.2*self.VSPACE*DOWN + 0.5*self.HSPACE*RIGHT
        start = end + 2*LEFT
        line = Line(start=start, end=end)

        self.play(FadeIn(addend), FadeIn(plus), FadeIn(line))
        self.wait(1)

        decL = TexMobject(r"A").scale(
            self.CARDSCALE).next_to(addend, DOWN).shift(DOWN*0.2)
        decH = TexMobject(r"9").scale(
            self.CARDSCALE).next_to(decL, LEFT)

        self.play(FadeIn(decL), FadeIn(decH))
        self.wait(1)

        addendL = TexMobject(r"6").scale(
            self.CARDSCALE).next_to(decL, DOWN)
        addendH = TexMobject(r"6").scale(
            self.CARDSCALE).next_to(decH, DOWN)
        plus = TexMobject(
            "+").scale(0.7 * self.CARDSCALE).next_to(decH, LEFT).shift(0.5*DOWN)
        end = addendL.get_corner(
            DOWN+RIGHT) + 0.2*self.VSPACE*DOWN + 0.5*self.HSPACE*RIGHT
        start = end + 2*LEFT
        line = Line(start=start, end=end)

        self.play(FadeIn(addendL), FadeIn(addendH), FadeIn(plus), FadeIn(line))
        self.wait(1)

        decL = TexMobject(r"0").scale(
            self.CARDSCALE).next_to(addendL, DOWN).shift(DOWN*0.2)
        decH = TexMobject(r"0").scale(
            self.CARDSCALE).next_to(decL, LEFT)
        carry = TexMobject(r"1").scale(
            0.5*self.CARDSCALE).next_to(decH, LEFT).align_to(decH, UP)

        self.play(FadeIn(decL), FadeIn(decH), FadeIn(carry))
        self.wait(1)

        # 99 + 99

        decL = TexMobject(r"9").scale(
            self.CARDSCALE).move_to(TOP, UP).shift(2 * DOWN + 2 * RIGHT)
        decH = TexMobject(r"9").scale(
            self.CARDSCALE).next_to(decL, LEFT)

        self.play(FadeIn(decL), FadeIn(decH))
        self.wait(1)

        addendL = TexMobject(r"9").scale(
            self.CARDSCALE).next_to(decL, DOWN)
        addendH = TexMobject(r"9").scale(
            self.CARDSCALE).next_to(decH, DOWN)
        plus = TexMobject(
            "+").scale(0.7 * self.CARDSCALE).next_to(decH, LEFT).shift(0.5*DOWN)
        end = addendL.get_corner(
            DOWN+RIGHT) + 0.2*self.VSPACE*DOWN + 0.5*self.HSPACE*RIGHT
        start = end + 2*LEFT
        line = Line(start=start, end=end)

        self.play(FadeIn(addendL), FadeIn(addendH), FadeIn(plus), FadeIn(line))
        self.wait(1)

        decL = TexMobject(r"2").scale(
            self.CARDSCALE).next_to(addendL, DOWN).shift(DOWN*0.2)
        decH = TexMobject(r"3").scale(
            self.CARDSCALE).next_to(decL, LEFT)
        carry1 = TexMobject(r"1").scale(
            0.5*self.CARDSCALE).next_to(decH, LEFT).align_to(decH, UP)

        self.play(FadeIn(decL), FadeIn(decH), FadeIn(carry1))
        self.wait(1)

        addendL = TexMobject(r"6").scale(
            self.CARDSCALE).next_to(decL, DOWN)
        addendH = TexMobject(r"6").scale(
            self.CARDSCALE).next_to(decH, DOWN)
        plus = TexMobject(
            "+").scale(0.7 * self.CARDSCALE).next_to(decH, LEFT).shift(0.5*DOWN)
        end = addendL.get_corner(
            DOWN+RIGHT) + 0.2*self.VSPACE*DOWN + 0.5*self.HSPACE*RIGHT
        start = end + 2*LEFT
        line = Line(start=start, end=end)

        self.play(FadeIn(addendL), FadeIn(addendH), FadeIn(plus), FadeIn(line))
        self.wait(1)

        decL = TexMobject(r"8").scale(
            self.CARDSCALE).next_to(addendL, DOWN).shift(DOWN*0.2)
        decH = TexMobject(r"9").scale(
            self.CARDSCALE).next_to(decL, LEFT)
        carry2 = TexMobject(r"1").scale(
            0.5*self.CARDSCALE).next_to(decH, LEFT).align_to(decH, UP)

        self.play(FadeIn(decL), FadeIn(decH), FadeIn(carry2))
        self.wait(1)

        for _ in range(4):
            self.play(ApplyMethod(carry1.scale, 1.5),
                      ApplyMethod(carry2.scale, 1.5), run_time=0.3)
            self.play(ApplyMethod(carry1.scale, 1/1.5),
                      ApplyMethod(carry2.scale, 1/1.5), run_time=0.3)
        self.wait(1)

    def storyboard12(self):
        self.fadeout_all()
        self.wait(1)

        t = TexMobject(r"\text{NO}").scale(2).center()
        self.play(FadeIn(t), run_time=0.2)
        self.wait(1)

        self.fadeout_all()
        self.wait(1)
