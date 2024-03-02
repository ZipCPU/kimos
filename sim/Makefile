################################################################################
##
## Filename:	sim/Makefile
## {{{
## Project:	KIMOS, a Mercury KX2 demonstration project
##
## Purpose:	To coordinate the build of a cycle accurate, Verilator based,
##		simulation of the main module.  Access to the simulation is
##	provided via the same software commands that will access the board, save
##	that the parameters are a touch different.  (See the access software for
##	more information ...)
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
## with this program.  (It's in the $(ROOT)/doc directory, run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
## }}}
.PHONY: all
# Make certain the "all" target is the first and therefore the default target
all:
CXX	:= g++
OBJDIR	:= obj-pc
RTLD	:= ../rtl
VOBJDR	:= $(RTLD)/obj_dir
VERILATOR_ROOT ?= $(shell bash -c 'verilator -V|grep VERILATOR_ROOT | head -1 | sed -e " s/^.*=\s*//"')
VROOT	:= $(VERILATOR_ROOT)
VVERSION:= vversion.sh
VDEFS    = $(shell bash $(VVERSION))
VINCD   := $(VROOT)/include
VINC	:= -I$(VINCD) -I$(VINCD)/vltstd -I$(VOBJDR)
INCS	:= -I. -I../sw/host -I$(RTLD) $(VINC)
CFLAGS	:= -O3 -faligned-new -Wall $(VDEFS) $(INCS)
#
# A list of our sources and headers
#
## COMMON sources across projects
SIMMODELS:= flashsim.cpp sdspisim.cpp dbluartsim.cpp enetctrlsim.cpp memsim.cpp sdiosim.cpp netsim.cpp udpsocket.cpp
AUXSOURCES:= zipelf.cpp byteswap.cpp # udpsocket.cpp
SIMSOURCES:= $(SIMMODELS) $(AUXSOURCES)
SIMOBJECTS:= $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SIMSOURCES)))
VOBJS   := $(OBJDIR)/verilated.o $(OBJDIR)/verilated_vcd_c.o $(OBJDIR)/verilated_threads.o
SIMOBJ := $(subst .cpp,.o,$(SIMSOURCES))
ALLOBJS:= $(addprefix $(OBJDIR)/,$(SIMOBJ)) $(VOBJS)

SOURCES := $(SIMSOURCES) main_tb.cpp automaster_tb.cpp
HEADERS := $(foreach header,$(subst .cpp,.h,$(SOURCES)),$(wildcard $(header)))
#
PROGRAMS := main_tb
# Now the return to the "all" target, and fill in some details
all:	$(PROGRAMS)

## Object-file build patterns
## {{{
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(VDEFS) $(INCS) -c $< -o $@

$(OBJDIR)/%.o: $(VINCD)/%.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) $(INCS) -c $< -o $@
## }}}


$(OBJDIR)/main_tb.o: $(VOBJDR)/Vmain.h
$(OBJDIR)/automaster_tb.o: $(VOBJDR)/Vmain.h
MAINOBJS := $(OBJDIR)/main_tb.o $(OBJDIR)/automaster_tb.o
main_tb: $(MAINOBJS) $(ALLOBJS) $(VOBJDR)/Vmain__ALL.a
	$(CXX) $(CFLAGS) $^ -lelf -lpthread -o $@

#
sdcard.img: # Build a 64M SD-card image file that we can use for testing
## {{{
	dd if=/dev/zero of=$@ bs=512 count=131072
	mkfs.fat $@
## }}}
#
.PHONY: cputest
## {{{
cputest: ../sw/board/cputest
	./main_tb -d ../sw/board/cputest
## }}}

.PHONY: test # The "test" target, running hello world
## {{{
test: cputest ../sw/board/hello
	./main_tb -d ../sw/board/hello
## }}}


#
# The "clean" target, removing any and all remaining build products
#
.PHONY: clean
clean:
	rm -f *.vcd
	rm -f $(PROGRAMS)
	rm -rf $(OBJDIR)/
.PHONY: hex cmem_hex
hex:	quadtbl_ctbl.hex quadtbl_ltbl.hex quadtbl_qtbl.hex cmem_hex
cmem_hex: cmem_8.hex cmem_16.hex cmem_32.hex cmem_64.hex cmem_128.hex	\
	cmem_256.hex cmem_512.hex cmem_1024.hex cmem_2048.hex hanning.hex
quadtbl_ctbl.hex:
	ln -s ../rtl/audio/quadtbl_ctbl.hex .
quadtbl_ltbl.hex:
	ln -s ../rtl/audio/quadtbl_ltbl.hex .
quadtbl_qtbl.hex:
	ln -s ../rtl/audio/quadtbl_qtbl.hex .
cmem_8.hex:
	ln -s ../rtl/video/fftcore/cmem_8.hex .
cmem_16.hex:
	ln -s ../rtl/video/fftcore/cmem_16.hex .
cmem_32.hex:
	ln -s ../rtl/video/fftcore/cmem_32.hex .
cmem_64.hex:
	ln -s ../rtl/video/fftcore/cmem_64.hex .
cmem_128.hex:
	ln -s ../rtl/video/fftcore/cmem_128.hex .
cmem_256.hex:
	ln -s ../rtl/video/fftcore/cmem_256.hex .
cmem_512.hex:
	ln -s ../rtl/video/fftcore/cmem_512.hex .
cmem_1024.hex:
	ln -s ../rtl/video/fftcore/cmem_1024.hex .
cmem_2048.hex:
	ln -s ../rtl/video/fftcore/cmem_2048.hex .
hanning.hex:
	ln -s ../rtl/video/hanning.hex .
#
# The "depends" target, to know what files things depend upon.  The depends
# file itself is kept in $(OBJDIR)/depends.txt
#
define build-depends
	$(mk-objdir)
	@echo "Building dependency file"
	@$(CXX) $(CFLAGS) $(INCS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: depends

#
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef


#
# The "tags" target
#
tags:	$(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)


ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
