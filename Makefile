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

# Run via:
# make -s formal
#
# This will run formal verifications for all instructions that haven't
# yet passed formal verification. That is, if formal verification
# fails on an instruction, you can run make -s formal again, and it will
# skip all instrutions that already verified properly, and pick up where
# the failure happened.
#
# Note that this generally doesn't help, since fixing the problem usually
# involves modifying core.py, which will then cause formal verification
# to begin anew.
#
# You can also run formal verification on one or more specific instructions
# via make -s formal_<insn> formal_<insn> ...

formal_targets := $(patsubst formal/%.py, %, $(wildcard formal/formal_*.py))

.PHONY: formal

formal: $(formal_targets)

formal_%: formal/sby/%_bmc/PASS
	$(info $(shell date '+%d %b %Y %H:%M:%S') Verified instruction '$*')

# Don't delete the status file if the user hits ctrl-C.
# .PRECIOUS: formal/sby/%_bmc/status

formal/sby/%_bmc/PASS: formal/sby/%.sby
	$(info $(shell date '+%d %b %Y %H:%M:%S') Running formal verification on instruction '$*'...)
	sby -f $< 2>&1 >/dev/null; if [ $$? -ne 0 ]; then \
		echo `date '+%d %b %Y %H:%M:%S'` Formal verification FAILED for instruction \'$*\'; \
	fi

formal/sby/%.sby: formal/sby/%.il formal/formal.sby
	mkdir -p formal/sby
	cat formal/formal.sby | sed --expression='s#rel_file#$*#g' | sed --expression='s#abs_file#formal/sby/$*#g' > $@

formal/sby/%.il: formal/formal_%.py core.py
	python3 core.py --insn $* generate -t il > $@

formal/sby/alu8.il: alu8.py
	python3 alu8.py generate -t il > $@
