################################################################################
##
## Filename:	sw/board/Makefile
## {{{
## Project:	KIMOS, a Mercury KX2 demonstration project
##
## Purpose:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
## }}}
.PHONY: all
PROGRAMS := hello cputest sdinfo sdiochk mdio # memtest # netcheck contest
all:	$(PROGRAMS)
#
#
CC	:=zip-gcc
AS	:=zip-as
LD	:=zip-ld
NM	:=zip-nm
OBJDIR	:= obj-zip
RDELF	:= zip-readelf
OBJDUMP := zip-objdump
SUBMAKE:= $(MAKE) --no-print-directory -C
#
#
# SOURCES := hello.c cputest.c memtest.c sdiochk.v sdinfo.c
SOURCES := $(wildcard *.c)
HEADERS :=
DUMPRTL := -fdump-rtl-all
DUMPTREE:= -fdump-tree-all
LDSCRIPT:= board.ld
LFLAGS  := -T $(LDSCRIPT) -L../zlib -L../fatfs
LBKRAM  := -T bkram.ld -L../zlib
CFLAGS  := -O3 -I../zlib -I../../rtl -I../fatfs
LIBS    := -lc -lzkim -lgcc
LIBFAT  := -lfatfs
INSTALLD=$(shell bash -c "which zip-gcc | sed -e 's/.cross-tools.*$\//'")
NLIBD=$(INSTALLD)/cross-tools/zip/lib
ZLIBD=../zlib
LIB=$(ZLIBD)/libzkim.a $(NLIBD)/libg.a $(NLIBD)/libc.a
FAT:=../fatfs/libfatfs.a
#

## Build macro templates
## {{{

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) $(DUMPRTL) -S $< -o $@
$(OBJDIR)/%.txt: $(OBJDIR)/%.o
	bash -c "$(RDELF) -a $^ ; $(OBJDUMP) -S -D $^ " | tee -a $@
%.txt: %
	$(OBJDUMP) -S -D $^ > $@
## }}}

## CPU Test
## {{{
#
# The CPUTest program here is special--it doesn't use the C library.  Hence,
# it must have the -fno-builtin flag in order to build, and the -Tartyram.ld
# linker script to build something that doesn't go into flash but directly into
# RAM instead.
#
$(OBJDIR)/cputest.o: cputest.c board.h
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-nocis -fno-builtin $< -o $@
$(OBJDIR)/cputestcis.o: cputest.c board.h
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-cis -fno-builtin $< -o $@
$(OBJDIR)/cputest.s: cputest.c
	$(CC) $(CFLAGS) -S -Wa,-cis -fno-builtin $< -o $@

cputest: $(OBJDIR)/cputestcis.o board.ld $(LIB)
	# $(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@
	$(CC) $(CFLAGS) $(LBKRAM) $< $(LIBS) -o $@
## }}}

## Hello World
## {{{
$(OBJDIR)/hello.o: hello.c
	$(CC) -O3 -c $< -o $@

hello: $(OBJDIR)/hello.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@
## }}}

mdio: $(OBJDIR)/mdio.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@

sdiochk: $(OBJDIR)/sdiochk.o $(OBJDIR)/txfns.o board.ld $(LIB)
	$(CC) $(CFLAGS) $(LBKRAM) $< $(OBJDIR)/txfns.o $(LIBS) -o $@

sdinfo: $(OBJDIR)/sdinfo.o $(OBJDIR)/txfns.o board.ld $(LIB) $(FAT)
	$(CC) $(CFLAGS) $(LFLAGS) $< $(OBJDIR)/txfns.o $(LIBFAT) $(LIBS) -o $@

# memtest: $(OBJDIR)/memtest.o bkram.ld $(LIB)
#	$(CC) $(CFLAGS) $(LBKRAM) $< $(LIBS) -o $@

## mk-objdir
## {{{
define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"
endef
## }}}

.PHONY: clean
## {{{
clean:
	rm -f $(PROGRAMS) hellosim
	rm -rf $(addsuffix .map,$(PROGRAMS))
	rm -rf $(addsuffix .txt,$(PROGRAMS))
	rm -rf $(OBJDIR)/
## }}}

## Dependency handling
## {{{
define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)
## }}}

ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
