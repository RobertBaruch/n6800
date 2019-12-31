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

    def construct(self):
        self.H = 0.8
        self.W = 0.5
        self.HSPACE = self.W * 1.3
        self.VSPACE = self.H * 1.4
        self.XPOS0 = 6*self.HSPACE*LEFT

        self.rectX = [self.card() for i in range(8)]
        self.rectY = [self.card() for i in range(8)]

        self.do(1, self.storyboard1)
        self.do(2, self.storyboard2)
        self.do(3, self.storyboard3)
        self.do(4, self.storyboard4)
        self.do(5, self.storyboard5)
        self.do(6, self.storyboard6)
        self.do(7, self.storyboard7)
        self.do(8, self.storyboard8)
        self.do(9, self.storyboard9)
        self.do(10, self.storyboard10)
        self.do(11, self.storyboard11)
        self.do(12, self.storyboard12)
        self.do(13, self.storyboard13)
        self.do(14, self.storyboard14)
        self.wait(5)

    def storyboard1(self):
        for i, r in enumerate(self.rectX):
            r.shift(RIGHT_SIDE + i*self.HSPACE *
                    LEFT + self.XPOS0 + self.VSPACE*UP)
        for i, r in enumerate(self.rectY):
            r.shift(RIGHT_SIDE + i*self.HSPACE*LEFT + self.XPOS0)

        for r in self.rectX:
            self.add(r)
        for r in self.rectY:
            self.add(r)

        self.play(LaggedStart(*(
            [FadeInFrom(r, direction=UP) for r in self.rectX] + [FadeInFrom(r, direction=UP) for r in self.rectY])), lag_ratio=0.1)

    def storyboard2(self):
        self.play(*[ApplyMethod(x.shift, 2*self.HSPACE*LEFT)
                    for x in [self.rectX[7], self.rectY[7]]])
        self.play(*[ApplyMethod(x.shift, self.HSPACE*LEFT)
                    for x in self.rectX[4:7] + self.rectY[4:7]])

    def storyboard3(self):
        start = self.rectY[7].get_corner(
            DOWN+LEFT) + 0.25*self.VSPACE*DOWN + 0.5*self.HSPACE*LEFT
        end = self.rectY[0].get_corner(
            DOWN+RIGHT) + 0.25*self.VSPACE*DOWN + 0.5*self.HSPACE*RIGHT

        self.line = Line(start=start, end=end)
        self.play(FadeIn(self.line))

        self.sum = [self.card() for i in range(8)]
        for i, s in enumerate(self.sum[0:4]):
            s.next_to(self.rectY[i], 2*self.VSPACE*DOWN)
        self.h = self.card()
        self.h.next_to(self.sum[3], self.HSPACE*LEFT)

        self.play(*[FadeIn(s) for s in self.sum[0:4] + [self.h]])
        self.wait(1)

        self.h.generate_target()
        self.h.target.next_to(self.rectX[4], self.VSPACE*UP)
        self.play(MoveToTarget(self.h))
        self.htext = TexMobject(r"\text{H}")
        self.htext.move_to(self.h.get_center())
        self.htext.scale(0.8)
        self.play(FadeIn(self.htext))
        self.h = Group(self.h, self.htext)

    def storyboard4(self):
        for i, s in enumerate(self.sum[4:7]):
            s.next_to(self.rectY[i+4], 2*self.VSPACE*DOWN)
        self.c7 = self.card()
        self.c7.next_to(self.sum[6], self.HSPACE*LEFT)

        self.play(*[FadeIn(s) for s in self.sum[4:7] + [self.c7]])
        self.wait(1)

        self.c7.generate_target()
        self.c7.target.next_to(self.rectX[7], self.VSPACE*UP)
        self.play(MoveToTarget(self.c7))

        self.c7text = TexMobject(r"\text{C}_7")
        self.c7text.move_to(self.c7.get_center())
        self.c7text.scale(0.8)
        self.play(FadeIn(self.c7text))
        self.c7 = Group(self.c7, self.c7text)

    def storyboard5(self):
        self.sum[7].next_to(self.rectY[7], 2*self.VSPACE*DOWN)
        self.c = self.card()
        self.c.next_to(self.sum[7], self.HSPACE*LEFT)

        self.play(*[FadeIn(s) for s in [self.sum[7], self.c]])
        self.wait(1)

        self.c.generate_target()
        self.c.target.next_to(self.rectX[7], self.VSPACE*UP+2*self.HSPACE*LEFT)
        self.play(MoveToTarget(self.c))

        self.ctext = TexMobject(r"\text{C}_8")
        self.ctext.move_to(self.c.get_center())
        self.ctext.scale(0.8)
        self.play(FadeIn(self.ctext))
        self.c = Group(self.c, self.ctext)

        self.wait(1)
        self.ctext.target = TexMobject(r"\text{C}")
        self.ctext.target.scale(0.8)
        self.ctext.target.move_to(self.c.get_center())
        self.play(MoveToTarget(self.ctext))

    def storyboard6(self):
        self.play(*[FadeOut(s) for s in self.rectX + self.rectY + [self.line]])
        self.play(*(
            [ApplyMethod(x.shift, 2*self.HSPACE*RIGHT) for x in [self.sum[7]]] +
            [ApplyMethod(x.shift, self.HSPACE*RIGHT) for x in self.sum[4:7]]))

    def storyboard7(self):
        self.play(ApplyMethod(self.c.shift, self.HSPACE*LEFT))

        self.v = self.card()
        self.v.move_to(self.c7.get_center() + 2*self.HSPACE*RIGHT)
        self.vtext = TexMobject(r"\text{V}")
        self.vtext.move_to(self.v.get_center())
        self.vtext.scale(0.8)
        self.v = Group(self.v, self.vtext)

        xor = TexMobject(r"xor")
        xor.move_to((self.c.get_center() + self.c7.get_center())/2)
        eq = TexMobject(r"=")
        eq.move_to((self.c7.get_center() + self.v.get_center())/2)

        self.play(Write(xor), Write(eq), FadeIn(self.v))
        self.wait(1)
        self.play(FadeOut(xor), FadeOut(eq), FadeOut(self.c7))

    def storyboard8(self):
        self.i = self.card()
        self.z = self.card()
        self.i.move_to(self.c.get_center() + 2 * self.HSPACE*RIGHT)
        self.z.move_to(self.c.get_center() + 4 * self.HSPACE*RIGHT)

        self.play(*[
            ApplyMethod(self.h.move_to, self.c.get_center() +
                        self.HSPACE*RIGHT),
            ApplyMethod(self.v.move_to, self.c.get_center() +
                        5 * self.HSPACE*RIGHT),
            ApplyMethod(self.c.move_to, self.c.get_center() +
                        6 * self.HSPACE*RIGHT),
        ])
        self.play(FadeIn(self.i), FadeIn(self.z))

        tmptext = TexMobject(r"\text{N}")
        tmptext.move_to(self.sum[7].get_center())
        tmptext.scale(0.8)
        self.play(FadeIn(tmptext))

        self.n = Group(self.sum[7].deepcopy(), tmptext.deepcopy())

        self.play(ApplyMethod(self.n.move_to,
                              self.h.get_center() + 2 * self.HSPACE*RIGHT))
        self.play(FadeOut(tmptext))

    def storyboard9(self):
        self.scanner = SurroundingRectangle(self.sum[0])
        self.scanner.shift(2*self.HSPACE*RIGHT)
        self.play(FadeIn(self.scanner))

        anims = []
        for s in self.sum:
            anims.append(Succession(
                ApplyMethod(s.set_fill, YELLOW, {"opacity": 1}, run_time=0.1),
                ApplyMethod(s.set_fill, BLACK, {"opacity": 1}, run_time=0.5)))

        anims = [ApplyMethod(self.scanner.move_to, self.sum[7].get_center(
        ) + 2*self.HSPACE*LEFT, run_time=1.8)] + anims
        self.play(LaggedStart(*anims, lag_ratio=0.18))

        tmptext = TexMobject(r"\text{Z}")
        tmptext.move_to(self.scanner.get_center())
        tmptext.scale(0.8)
        tmpz = self.card()
        tmpz.move_to(self.scanner.get_center())
        tmpz = Group(tmpz, tmptext)

        self.play(FadeOut(self.scanner), FadeIn(tmpz))
        self.play(Succession(
            ApplyMethod(tmpz.move_to, self.z.get_center()),
            FadeOut(self.z, run_time=0)))
        self.z = tmpz

    def storyboard10(self):
        self.fadeout_all()
        self.wait(2)

        sum = Group(*self.sum)
        addends = Group(*(self.rectX + self.rectY))
        self.sum[7].shift(2*self.HSPACE*LEFT)
        for x in self.sum[4:7]:
            x.shift(self.HSPACE*LEFT)

        self.play(FadeIn(addends), FadeIn(self.line), FadeIn(sum))

        self.c.move_to(self.rectX[0].get_center() + self.VSPACE*UP)
        self.c.set_x(FRAME_X_RADIUS + 2*self.HSPACE)
        self.play(ApplyMethod(self.c.move_to,
                              self.rectX[0].get_center() + self.VSPACE*UP))

    def storyboard11(self):
        self.fadeout_all()
        self.wait(2)

        negx = TexMobject(r"-X")
        negx.scale(2)
        self.play(FadeIn(negx))

        self.play(ApplyMethod(negx.shift, 2*LEFT))

        eq = TexMobject(r"=\bar{X}+1")
        eq.scale(2)
        eq.next_to(negx, RIGHT)
        self.play(Write(eq))
        self.negative_eqn = Group(negx, eq)

    def storyboard12(self):
        self.sum[7].shift(2*self.HSPACE*RIGHT)
        for s in self.sum[4:7]:
            s.shift(self.HSPACE*RIGHT)

        text = TexMobject(r"1")
        text.scale(1.2)
        text.move_to(self.sum[0].get_center())
        self.sum_text = [text]
        self.sum_nums = [Group(self.sum[0], text)]

        for s in self.sum[1:]:
            text = TexMobject(r"0")
            text.scale(1.2)
            text.move_to(s.get_center())
            self.sum_text.append(text)
            self.sum_nums.append(Group(s, text))

        sum = Group(*self.sum_nums)
        sum.move_to(0)

        self.negative_eqn.generate_target()
        self.negative_eqn.target.shift(2*UP).scale(0.7)
        self.play(MoveToTarget(self.negative_eqn))
        self.play(FadeIn(sum))
        self.wait(1)

        anims = []
        for i, s in enumerate(self.sum_text):
            text = TexMobject(r"0") if i == 0 else TexMobject(r"1")
            text.scale(1.2)
            text.move_to(self.sum[i].get_center())
            anims.append(Transform(s, text))
        self.play(*anims)
        self.wait(1)

        newtext = TexMobject(r"1").scale(1.2).move_to(self.sum[0].get_center())
        self.play(FadeInFrom(newtext, DOWN),
                  FadeOutAndShift(self.sum_text[0], UP))

        self.sum_text[0] = newtext
        self.sum_nums[0] = Group(self.sum[0], newtext)
        self.wait(1)

    def storyboard13(self):
        sum = Group(*self.sum_nums)
        self.play(FadeOut(sum))
        self.wait(1)

        eq1_text = ["A-B-0", "=", "A+(-B)-0", "=", r"A+\bar{B}+1"]
        eq2_text = ["A-B-1", "=", "A+(-B)-1", "=", r"A+\bar{B}+0"]
        eq3_text = ["A-B-C", "=", "A+(-B)-C", "=", r"A+\bar{B}+\bar{C}"]

        eq1 = TexMobject(*eq1_text)
        eq2 = TexMobject(*eq2_text)
        eq3 = TexMobject(*eq3_text)

        for i, item in enumerate(eq1):
            item.align_to(eq3[i], LEFT)
        for i, item in enumerate(eq2):
            item.align_to(eq3[i], LEFT)

        eq1 = VGroup(*eq1)
        eq2 = VGroup(*eq2)
        eq3 = VGroup(*eq3)
        eq2.shift(DOWN)
        eq3.shift(2 * DOWN)

        self.play(FadeIn(eq1))
        self.wait(1)
        self.play(FadeIn(eq2))
        self.wait(1)
        self.play(FadeIn(eq3))
        self.wait(1)
        self.fadeout_all()
        self.wait(1)

    def storyboard14(self):
        self.sum = [self.card() for i in range(8)]
        for i, s in enumerate(self.sum):
            s.next_to(self.rectY[i], 2*self.VSPACE*DOWN)

        sum = Group(*self.sum)
        addends = Group(*(self.rectX + self.rectY))
        tilde = TexMobject(r"\sim(").scale(2)
        rparen = TexMobject(r")").scale(2)
        tilde.next_to(self.rectY[7], LEFT)
        rparen.next_to(self.rectY[0], RIGHT)
        self.play(
            FadeIn(Group(*self.rectX)), FadeIn(Group(*self.rectY)
                                               ), FadeIn(self.line), FadeIn(sum),
            FadeIn(tilde), FadeIn(rparen))

        self.c.move_to(self.rectX[0].get_center() + self.VSPACE*UP)
        self.c.set_x(FRAME_X_RADIUS + 2*self.HSPACE)
        self.play(ApplyMethod(self.c.move_to,
                              self.rectX[0].get_center() + self.VSPACE*UP))
        self.wait(1)

        c = self.c[1]
        c_bar = TexMobject(r"\bar{\text{C}}").scale(
            0.8).move_to(self.c.get_center())
        self.c = Group(self.c[0], c_bar)
        self.play(FadeOutAndShift(c, LEFT), FadeInFrom(c_bar, RIGHT))
        self.wait(1)

        c = TexMobject(r"\text{C}").scale(0.8).move_to(self.c.get_center())
        c_copy = Group(self.c[0].deepcopy(), c)
        c_copy.next_to(self.rectX[7], self.VSPACE*UP+2*self.HSPACE*LEFT)
        self.play(FadeIn(c_copy))
        self.wait(1)

        c_bar = TexMobject(r"\bar{\text{C}}").scale(
            0.8).move_to(c_copy.get_center())
        c_copy = Group(c_copy[0], c_bar)
        self.play(FadeOutAndShift(c, LEFT), FadeInFrom(c_bar, RIGHT))
        self.wait(1)

        print(
            f"Before fadeout there are {len(self.get_mobjects())} mobjects and {len(self.foreground_mobjects)} foreground mobjects in the scene left")

        self.fadeout_all()
