################################################################################
##
## Filename:	autodata/Makefile
## {{{
## Project:	KIMOS, a Mercury KX2 demonstration project
##
## Purpose:	To direct the build of the autofpga automatically generated
##		files.  The various configuration files are the *.txt files
##	found in this directory.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
all:	data
#
# Could also depend upon load, if desired, but not necessary
#
# This is the list of components that will form our project.  Each file consists
# of parts and pieces of our project that autofpga will copy/paste into our
# main project files.
#
BASE    := global.txt crossbus.txt icape.txt
AUX     := version.txt pic.txt pwrcount.txt rtccount.txt # buserr.txt
IO      := spio.txt # gpio.txt
RTC     := #
DBGBUS  := exconsole.txt wbuuart.txt wbuarbiter.txt
MEMORY  := bkram.txt flash.txt flashcfg.txt sdram.txt # ddr3.txt bkrom.txt
CPU     := zipmaster.txt
NETWORK := mdio.txt meganet.txt protocols.txt # netbus.txt # cpunet.txt # eth1.txt eth1cpu.txt
SDCARD  := sdio.txt
SCOPES  := # netscope.txt i2cscope.txt sdscope.txt cpuscope.txt
CLOCKS  := allclocks.txt clkcheck.txt # sclk.txt
OTHER   := xdc.txt
LDSCRIPT:= mem_flash_bkram.txt mem_sdram_only.txt mem_flash_sdram.txt mem_bkram_only.txt
# LDSCRIPT:= mem_bkram_only.txt mem_bootrom_bkram.txt
# GFX     := # The KX2 base board has no video resources
# AUDIO   := # The KX2 base board has no audio resources
DATA := $(CLOCKS) $(BASE) $(AUX) $(IO) $(RTC) $(SONAR)		\
	$(DBGBUS) $(MEMORY) $(CPU) $(NETWORK) $(SDCARD)		\
	$(SCOPES) $(LDSCRIPT) $(OTHER)

AUTOFPGA := autofpga
$(AUTOFPGA):

.PHONY: data
data: $(AUTOFPGA) $(DATA)
	$(AUTOFPGA) -I $(COMMON)/ -d -o . $(DATA)

.PHONY: clean
## {{{
clean:
	rm -f toplevel.v main.v regdefs.h regdefs.cpp board.h board.ld
	rm -f rtl.make.inc main_tb.cpp
	rm -f dump.txt
## }}}
