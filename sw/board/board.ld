/*******************************************************************************
*
* Filename:	board.ld
* {{{
* Project:	KIMOS, a Mercury KX2 demonstration project
*
* Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
* DO NOT EDIT THIS FILE!
*
* CmdLine:	autofpga -I / -d -o . allclocks.txt clkcheck.txt global.txt crossbus.txt icape.txt version.txt pic.txt pwrcount.txt rtccount.txt spio.txt exconsole.txt wbuuart.txt wbuarbiter.txt bkram.txt flash.txt flashcfg.txt ddr3.txt mem_sdram_only.txt mem_flash_sdram.txt zipmaster.txt mdio.txt meganet.txt protocols.txt eth0bus.txt sdio.txt flashscope.txt mem_flash_bkram.txt mem_bkram_only.txt xdc.txt i2ccpu.txt
*
* Creator:	Dan Gisselquist, Ph.D.
*		Gisselquist Technology, LLC
*
/*******************************************************************************
* }}}
* Copyright (C) 2024, Gisselquist Technology, LLC
* {{{
* This file is part of the KIMOS project.
*
* The KIMOS project is free software and gateware: you can redistribute it
* and/or modify it under the terms of the GNU General Public License as
* published by the Free Software Foundation, either version 3 of the License,
* or (at your option) any later version.
*
* This program is distributed in the hope that it will be useful, but WITHOUT
* ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
* FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
* for more details.
*
* You should have received a copy of the GNU General Public License along
* with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
* target there if the PDF file isn't present.)  If not, see
* <http://www.gnu.org/licenses/> for a copy.
* }}}
* License:	GPL, v3, as defined and found on www.gnu.org,
* {{{
*		http://www.gnu.org/licenses/gpl.html
*
/*******************************************************************************
*
* }}}
*/
ENTRY(_start)

MEMORY
{
	/* To be listed here, a slave must be of type MEMORY.  If the slave
	* has a defined name in its @LD.NAME tag, it will be listed here
	* under that name, otherwise it will be listed under it's
	* @$(PREFIX) tag with an underscore prepended to it.  The permissions
	* are given by the @LD.PERM tag.  Allowable permissions include
	* 'r' (read only), 'rx' (read and execute, but no writes),
	* 'wx' (read, write, and execute).  If no permission tag exists, a
	* permission of 'r' will be assumed.
	*/
	   flash(rx) : ORIGIN = 0x04000000, LENGTH = 0x04000000
	   bkram(wx) : ORIGIN = 0x0a000000, LENGTH = 0x00040000
	   sdram(wx) : ORIGIN = 0x40000000, LENGTH = 0x40000000
}

/* For each defined memory peripheral, we also define a pointer to that
* memory.  The name of this pointer is given by the @LD.NAME tag within
* the memory peripheral's configuration
*/
_flash    = ORIGIN(flash);
_bkram    = ORIGIN(bkram);
_sdram    = ORIGIN(sdram);
/* LD.DEFNS from zipmaster.txt */
_kram  = 0; /* No high-speed kernel RAM */
_ram   = ORIGIN(bkram);
_rom   = ORIGIN(flash);
_top_of_stack = ORIGIN(bkram) + LENGTH(bkram);


/* LD.DEFNS from zipmaster.txt */
_kram  = ORIGIN(bkram); /* No high-speed kernel RAM */
_ram   = ORIGIN(sdram);
_rom   = ORIGIN(flash);
_top_of_stack = ORIGIN(sdram) + LENGTH(sdram);


/* LD.SCRIPT from zipmaster.txt */
SECTIONS
{
       .rocode 0x04c00000 : ALIGN(4) {
               _boot_address = .;
               *(.start) *(.boot)
               *(.text.startup)
       } > flash
       _kram_start = . ;
       .kernel : ALIGN_WITH_INPUT {
               *(.kernel)
		}> bkram AT> flash
	_kram_end = .;
       _ram_image_start = . ;
       .text : ALIGN_WITH_INPUT {
               *(.text*)
               *(.rodata*) *(.strings)
               *(.data) *(COMMON)
               }> sdram AT> flash
       _ram_image_end = . ;
       .bss : ALIGN_WITH_INPUT {
               *(.bss)
               _bss_image_end = . ;
               } > sdram
       _top_of_heap = .;
}

