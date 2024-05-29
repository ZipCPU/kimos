################################################################################
##
## Filename:	sw/host/Makefile
## {{{
## Project:	KIMOS, a Mercury KX2 demonstration project
##
## Purpose:	Directs the build of a variety of host support programs.  These
##		programs are then used when interacting with the hardware
##	device.
##
##	exregs	Is the primary program for interacting with individual registers
##		within the design.
##
##	zipload	Used for loading ZipCPU programs into memory, whether flash,
##		block RAM, or DDR3 SDRAM, and then starting them.  Can also
##		be used to load an FPGA configuration into the device.
##
##	zipstate	Reads the current status/state from the ZipCPU, and
##		decodes it into a more human readable form.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2024, Gisselquist Technology, LLC
## {{{
## This file is part of the KIMOS project.
##
## The KIMOS project is free software and gateware: you can redistribute it
## and/or modify it under the terms of the GNU General Public License as
## published by the Free Software Foundation, either version 3 of the License,
## or (at your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
.PHONY: all
all:
## }}}
#
# Defines and directories
## {{{
CXX := g++
OBJDIR := obj-pc
SCOPES := flashscope mdioscope wb2axiscope sdioscope ddr3scope
SCOPESRCS := $(addsuffix .cpp,$(SCOPES))
BUSSRCS   := exbus.cpp devbus.cpp regdefs.cpp llcomms.cpp byteswap.cpp flashdrvr.cpp nexbus.cpp udpsocket.cpp
BUSOBJS   := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(BUSSRCS)))
MAINPROG  := excheck exregs exuart flashid zipload zipstate zipdbg
SOURCES   := $(addsuffix .cpp,$(MAINPROG)) zipelf.cpp twoc.cpp byteswap.cpp $(BUSSRCS) $(SCOPESRCS)
HEADERS   := $(wildcard $(addsuffix .h,$(MAINPROG))) $(wildcard $(subst .cpp,.h,$(BUSSRCS)))
OBJECTS   := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SOURCES)))
tmp:
	@echo $(BUSOBJS)
CFLAGS    := -Og -g -Wall -I. -I../../rtl
LIBS :=
## }}}
PROGRAMS := $(MAINPROG) $(SCOPES)
all: $(PROGRAMS)

## Default (object-file) build target formulas
## {{{
%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@
## }}}

## Executable build instructions
## {{{
## %: $(OBJDIR)/%.o $(BUSOBJS)
##	$(CXX) $(CFLAGS) $^ -o $@
exuart: $(OBJDIR)/exuart.o
	$(CXX) $(CFLAGS) $^ -o $@
excheck: $(OBJDIR)/excheck.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
exregs: $(OBJDIR)/exregs.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
ddr3scope: $(OBJDIR)/ddr3scope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
flashscope: $(OBJDIR)/flashscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
flashid: $(OBJDIR)/flashid.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
mdioscope: $(OBJDIR)/mdioscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
sdioscope: $(OBJDIR)/sdioscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
wb2axiscope: $(OBJDIR)/wb2axiscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
zipload: $(OBJDIR)/zipload.o $(BUSOBJS) $(OBJDIR)/zipelf.o
	$(CXX) $(CFLAGS) $^ -lelf -o $@
zipdbg: $(OBJDIR)/zipdbg.o $(BUSOBJS) $(OBJDIR)/zopcodes.o $(OBJDIR)/twoc.o
	$(CXX) $(CFLAGS) $^ -lcurses -o $@
zipstate: $(OBJDIR)/zipstate.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
## }}}

.PHONY: clean
## {{{
clean:
	rm -rf obj-pc
	rm -f $(PROGRAMS)
## }}}

## mk-objdir
## {{{
##
## Creates a directory for object files if it doesn't exist already
##
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef
## }}}

## Dependency infrastrucure
## {{{
## build-depends
## {{{
define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CXX) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef
## }}}

.PHONY: tags
## {{{
tags: $(SOURCES) $(HEADERS)
	@echo "Generating exuberant C-tags"
	@ctags $(SOURCES) $(HEADERS)
## }}}

.PHONY: depends
## {{{
depends: tags
	$(build-depends)
## }}}

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)
## }}}

## Include dependency info
## {{{
ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),depends)
-include $(OBJDIR)/depends.txt
endif
endif
## }}}
