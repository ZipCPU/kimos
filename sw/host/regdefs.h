////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./regdefs.h
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// DO NOT EDIT THIS FILE!
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga -I / -d -o . allclocks.txt clkcheck.txt global.txt crossbus.txt icape.txt version.txt pic.txt pwrcount.txt rtccount.txt spio.txt exconsole.txt wbuuart.txt wbuarbiter.txt bkram.txt flash.txt flashcfg.txt sdram.txt zipmaster.txt sdio.txt mem_flash_bkram.txt mem_sdram_only.txt mem_flash_sdram.txt mem_bkram_only.txt xdc.txt
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
// {{{
// This file is part of the KIMOS project.
//
// The KIMOS project is free software and gateware: you can redistribute it
// and/or modify it under the terms of the GNU General Public License as
// published by the Free Software Foundation, either version 3 of the License,
// or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
// }}}
#ifndef	REGDEFS_H
#define	REGDEFS_H


//
// The @REGDEFS.H.INCLUDE tag
//
// @REGDEFS.H.INCLUDE for masters
// @REGDEFS.H.INCLUDE for peripherals
// And finally any master REGDEFS.H.INCLUDE tags
// End of definitions from REGDEFS.H.INCLUDE


//
// Register address definitions, from @REGS.#d
//
// SDIO SD Card addresses
#define	R_SDIO_CTRL     	0x00000000	// 00000000, wbregs names: SDCARD
#define	R_SDIO_DATA     	0x00000004	// 00000000, wbregs names: SDDATA
#define	R_SDIO_FIFOA    	0x00000008	// 00000000, wbregs names: SDFIFOA, SDFIF0, SDFIFA
#define	R_SDIO_FIFOB    	0x0000000c	// 00000000, wbregs names: SDFIFOB, SDFIF1, SDFIFB
#define	R_SDIO_PHY      	0x00000010	// 00000000, wbregs names: SDPHY
#define	R_FLASH         	0x04000000	// 04000000, wbregs names: FLASH
// FLASH erase/program configuration registers
#define	R_FLASHCFG      	0x08000400	// 08000400, wbregs names: FLASHCFG, QSPIC
// CONSOLE registers
#define	R_CONSOLE_FIFO  	0x08000504	// 08000500, wbregs names: UFIFO
#define	R_CONSOLE_UARTRX	0x08000508	// 08000500, wbregs names: RX
#define	R_CONSOLE_UARTTX	0x0800050c	// 08000500, wbregs names: TX
// SYSCLK Clock Counter (measures clock speed)
#define	R_ADCCLK        	0x08000600	// 08000600, wbregs names: ADCCLK
#define	R_BUILDTIME     	0x08000604	// 08000604, wbregs names: BUILDTIME
#define	R_PIC           	0x08000608	// 08000608, wbregs names: PIC
#define	R_PWRCOUNT      	0x0800060c	// 0800060c, wbregs names: PWRCOUNT
#define	R_RTCCOUNT      	0x08000610	// 08000610, wbregs names: RTCCOUNT
// SYSCLK Clock Counter (measures clock speed)
#define	R_RXETH0CK      	0x08000614	// 08000614, wbregs names: RXETH0CK
#define	R_SPIO          	0x08000618	// 08000618, wbregs names: SPIO
// SYSCLK Clock Counter (measures clock speed)
#define	R_TXCLK         	0x0800061c	// 0800061c, wbregs names: TXCLK
#define	R_VERSION       	0x08000620	// 08000620, wbregs names: VERSION
// FPGA CONFIG REGISTERS: 0x4e0-0x4ff
#define	R_CFG_CRC       	0x08000700	// 08000700, wbregs names: FPGACRC
#define	R_CFG_FAR       	0x08000704	// 08000700, wbregs names: FPGAFAR
#define	R_CFG_FDRI      	0x08000708	// 08000700, wbregs names: FPGAFDRI
#define	R_CFG_FDRO      	0x0800070c	// 08000700, wbregs names: FPGAFDRO
#define	R_CFG_CMD       	0x08000710	// 08000700, wbregs names: FPGACMD
#define	R_CFG_CTL0      	0x08000714	// 08000700, wbregs names: FPGACTL0
#define	R_CFG_MASK      	0x08000718	// 08000700, wbregs names: FPGAMASK
#define	R_CFG_STAT      	0x0800071c	// 08000700, wbregs names: FPGASTAT
#define	R_CFG_LOUT      	0x08000720	// 08000700, wbregs names: FPGALOUT
#define	R_CFG_COR0      	0x08000724	// 08000700, wbregs names: FPGACOR0
#define	R_CFG_MFWR      	0x08000728	// 08000700, wbregs names: FPGAMFWR
#define	R_CFG_CBC       	0x0800072c	// 08000700, wbregs names: FPGACBC
#define	R_CFG_IDCODE    	0x08000730	// 08000700, wbregs names: FPGAIDCODE
#define	R_CFG_AXSS      	0x08000734	// 08000700, wbregs names: FPGAAXSS
#define	R_CFG_COR1      	0x08000738	// 08000700, wbregs names: FPGACOR1
#define	R_CFG_WBSTAR    	0x08000740	// 08000700, wbregs names: WBSTAR
#define	R_CFG_TIMER     	0x08000744	// 08000700, wbregs names: CFGTIMER
#define	R_CFG_BOOTSTS   	0x08000758	// 08000700, wbregs names: BOOTSTS
#define	R_CFG_CTL1      	0x08000760	// 08000700, wbregs names: FPGACTL1
#define	R_CFG_BSPI      	0x0800077c	// 08000700, wbregs names: FPGABSPI
#define	R_BKRAM         	0x0a000000	// 0a000000, wbregs names: RAM
#define	R_SDRAM         	0x40000000	// 40000000, wbregs names: SDRAM
// ZipCPU control/debug registers
#define	R_ZIPCTRL       	0x80000000	// 80000000, wbregs names: CPU, ZIPCTRL
#define	R_ZIPREGS       	0x80000080	// 80000000, wbregs names: ZIPREGS
#define	R_ZIPS0         	0x80000080	// 80000000, wbregs names: SR0
#define	R_ZIPS1         	0x80000084	// 80000000, wbregs names: SR1
#define	R_ZIPS2         	0x80000088	// 80000000, wbregs names: SR2
#define	R_ZIPS3         	0x8000008c	// 80000000, wbregs names: SR3
#define	R_ZIPS4         	0x80000090	// 80000000, wbregs names: SR4
#define	R_ZIPS5         	0x80000094	// 80000000, wbregs names: SR5
#define	R_ZIPS6         	0x80000098	// 80000000, wbregs names: SR6
#define	R_ZIPS7         	0x8000009c	// 80000000, wbregs names: SR7
#define	R_ZIPS8         	0x800000a0	// 80000000, wbregs names: SR8
#define	R_ZIPS9         	0x800000a4	// 80000000, wbregs names: SR9
#define	R_ZIPS10        	0x800000a8	// 80000000, wbregs names: SR10
#define	R_ZIPS11        	0x800000ac	// 80000000, wbregs names: SR11
#define	R_ZIPS12        	0x800000b0	// 80000000, wbregs names: SR12
#define	R_ZIPSSP        	0x800000b4	// 80000000, wbregs names: SSP, SR13
#define	R_ZIPCC         	0x800000b8	// 80000000, wbregs names: ZIPCC, CC, SCC, SR14
#define	R_ZIPPC         	0x800000bc	// 80000000, wbregs names: ZIPPC, PC, SPC, SR15
#define	R_ZIPUSER       	0x800000c0	// 80000000, wbregs names: ZIPUSER
#define	R_ZIPU0         	0x800000c0	// 80000000, wbregs names: UR0
#define	R_ZIPU1         	0x800000c4	// 80000000, wbregs names: UR1
#define	R_ZIPU2         	0x800000c8	// 80000000, wbregs names: UR2
#define	R_ZIPU3         	0x800000cc	// 80000000, wbregs names: UR3
#define	R_ZIPU4         	0x800000d0	// 80000000, wbregs names: UR4
#define	R_ZIPU5         	0x800000d4	// 80000000, wbregs names: UR5
#define	R_ZIPU6         	0x800000d8	// 80000000, wbregs names: UR6
#define	R_ZIPU7         	0x800000dc	// 80000000, wbregs names: UR7
#define	R_ZIPU8         	0x800000e0	// 80000000, wbregs names: UR8
#define	R_ZIPU9         	0x800000e4	// 80000000, wbregs names: UR9
#define	R_ZIPU10        	0x800000e8	// 80000000, wbregs names: SR10
#define	R_ZIPU11        	0x800000ec	// 80000000, wbregs names: SR11
#define	R_ZIPU12        	0x800000f0	// 80000000, wbregs names: SR12
#define	R_ZIPUSP        	0x800000f4	// 80000000, wbregs names: USP, UR13
#define	R_ZIPUCC        	0x800000f8	// 80000000, wbregs names: ZIPUCC, UCC
#define	R_ZIPUPC        	0x800000fc	// 80000000, wbregs names: ZIPUPC, UPC
#define	R_ZIPSYSTEM     	0x80000100	// 80000000, wbregs names: ZIPSYSTEM, ZIPSYS


//
// The @REGDEFS.H.DEFNS tag
//
// @REGDEFS.H.DEFNS for masters
#define	BAUDRATE	1000000
// @REGDEFS.H.DEFNS for peripherals
#define	SDRAMBASE	0x40000000
#define	SDRAMLEN	0x40000000
#define	BKRAMBASE	0x0a000000
#define	BKRAMLEN	0x00040000
#define	FLASHBASE	0x04000000
#define	FLASHLEN	0x04000000
#define	FLASHLGLEN	26
//
#define	FLASH_RDDELAY	1
#define	FLASH_NDUMMY	6
//
// @REGDEFS.H.DEFNS at the top level
// End of definitions from REGDEFS.H.DEFNS
//
// The @REGDEFS.H.INSERT tag
//
// @REGDEFS.H.INSERT for masters
// @REGDEFS.H.INSERT for peripherals
////////////////////////////////////////////////////////////////////////////////
//
// ZipCPU register definitions
// {{{

#define	CPU_GO		0x0000
#define	CPU_HALT	0x0001
#define	CPU_STALL	0x0002
#define	CPU_STEP	0x0004
#define	CPU_RESET	0x0008
#define	CPU_CLRCACHE	0x0010
// (Reserved)		0x00e0
#define	CPU_SLEEPING	0x0100
#define	CPU_GIE		0x0200
#define	CPU_INT		0x0400
#define	CPU_BREAK	0x0800
#define	CPU_EXINT	0xfffff000
//
#define	CPU_sR0		0x0020
#define	CPU_sSP		0x002d
#define	CPU_sCC		0x002e
#define	CPU_sPC		0x002f
#define	CPU_uR0		0x0030
#define	CPU_uSP		0x003d
#define	CPU_uCC		0x003e
#define	CPU_uPC		0x003f

#ifdef	BKROM_ACCESS
#define	RESET_ADDRESS	@$[0x%08x](bkrom.REGBASE)
#else
#ifdef	FLASH_ACCESS
#define	RESET_ADDRESS	0x04600000
#else
#define	RESET_ADDRESS	0x0a000000
#endif	// FLASH_ACCESS
#endif	// BKROM_ACCESS
// }}}
// Flash control constants
#define	QSPI_FLASH	// This core and hardware support a Quad SPI flash
#define	SZPAGEB		256
#define	PGLENB		256
#define	SZPAGEW		64
#define	PGLENW		64
#define	NPAGES		256
#define	SECTORSZB	(NPAGES * SZPAGEB)	// In bytes, not words!!
#define	SECTORSZW	(NPAGES * SZPAGEW)	// In words
#define	NSECTORS	64
#define	SECTOROF(A)	((A) & (-1<<16))
#define	SUBSECTOROF(A)	((A) & (-1<<12))
#define	PAGEOF(A)	((A) & (-1<<8))

// @REGDEFS.H.INSERT from the top level
typedef	struct {
	unsigned	m_addr;
	const char	*m_name;
} REGNAME;

extern	const	REGNAME	*bregs;
extern	const	int	NREGS;
// #define	NREGS	(sizeof(bregs)/sizeof(bregs[0]))

extern	unsigned	addrdecode(const char *v);
extern	const	char *addrname(const unsigned v);
// End of definitions from REGDEFS.H.INSERT


#endif	// REGDEFS_H