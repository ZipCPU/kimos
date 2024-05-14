////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./regdefs.h
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga -I / -d -o . allclocks.txt clkcheck.txt global.txt crossbus.txt icape.txt version.txt pic.txt pwrcount.txt rtccount.txt spio.txt exconsole.txt wbuuart.txt wbuarbiter.txt bkram.txt flash.txt flashcfg.txt sdram.txt mem_sdram_only.txt mem_flash_sdram.txt zipmaster.txt mdio.txt meganet.txt protocols.txt eth0bus.txt sdio.txt flashscope.txt sdioscope.txt mem_flash_bkram.txt mem_bkram_only.txt xdc.txt i2ccpu.txt
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
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
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
#ifndef	FPGAPORT
#define	FPGAPORT	5927
#define	UARTDBGPORT	5927
#define	UARTPORT	5928
#define	UDP_DBGPORT	5929
#define	UDP_DATAPORT	5930
#endif
// And finally any master REGDEFS.H.INCLUDE tags
// End of definitions from REGDEFS.H.INCLUDE


//
// Register address definitions, from @REGS.#d
//
// SDIO SD Card addresses
#define	R_SDIO_CTRL     	0x02000000	// 02000000, wbregs names: SDCARD
#define	R_SDIO_DATA     	0x02000004	// 02000000, wbregs names: SDDATA
#define	R_SDIO_FIFOA    	0x02000008	// 02000000, wbregs names: SDFIFOA, SDFIF0, SDFIFA
#define	R_SDIO_FIFOB    	0x0200000c	// 02000000, wbregs names: SDFIFOB, SDFIF1, SDFIFB
#define	R_SDIO_PHY      	0x02000010	// 02000000, wbregs names: SDPHY
#define	R_FLASH         	0x04000000	// 04000000, wbregs names: FLASH
// FLASH erase/program configuration registers
#define	R_FLASHCFG      	0x08000400	// 08000400, wbregs names: FLASHCFG, QSPIC
// flashdbg compressed scope
#define	R_FLASHSCOPE    	0x08000500	// 08000500, wbregs names: FLASHSCOPE
#define	R_FLASHSCOPED   	0x08000504	// 08000500, wbregs names: FLASHSCOPED
// sdioscope compressed scope
#define	R_SDIOSCOPE     	0x08000600	// 08000600, wbregs names: SDIOSCOPE
#define	R_SDIOSCOPED    	0x08000604	// 08000600, wbregs names: SDIOSCOPED
// I2C Controller registers
#define	R_I2CCPU        	0x08000700	// 08000700, wbregs names: I2CCPU, I2CCPU_CTRL, I2CCPUCTRL
#define	R_I2CCPU_OVW    	0x08000704	// 08000700, wbregs names: I2CCPU_OVW, I2CCPU_OVERRIDE
#define	R_I2CCPU_ADDR   	0x08000708	// 08000700, wbregs names: I2CCPU_ADDR, I2CCPU_ADDRESS
#define	R_I2CCPU_CKCOUNT	0x0800070c	// 08000700, wbregs names: I2CCPUCLK, I2CCPU_CKCOUNT
#define	R_I2CDMA        	0x08000800	// 08000800, wbregs names: I2CDMA
#define	R_I2CDMA_ADDR   	0x08000804	// 08000800, wbregs names: I2CDMAADDR
#define	R_I2CDMA_BASE   	0x08000808	// 08000800, wbregs names: I2CDMABASE
#define	R_I2CDMA_LEN    	0x0800080c	// 08000800, wbregs names: I2CDMALEN
// CONSOLE registers
#define	R_CONSOLE_FIFO  	0x08000904	// 08000900, wbregs names: UFIFO
#define	R_CONSOLE_UARTRX	0x08000908	// 08000900, wbregs names: RX, RXUART
#define	R_CONSOLE_UARTTX	0x0800090c	// 08000900, wbregs names: TX, TXUART
// SYSCLK Clock Counter (measures clock speed)
#define	R_ADCCLK        	0x08000a00	// 08000a00, wbregs names: ADCCLK
#define	R_BUILDTIME     	0x08000a04	// 08000a04, wbregs names: BUILDTIME
#define	R_PIC           	0x08000a08	// 08000a08, wbregs names: PIC
#define	R_PWRCOUNT      	0x08000a0c	// 08000a0c, wbregs names: PWRCOUNT
#define	R_RTCCOUNT      	0x08000a10	// 08000a10, wbregs names: RTCCOUNT
// SYSCLK Clock Counter (measures clock speed)
#define	R_RXETH0CK      	0x08000a14	// 08000a14, wbregs names: RXETH0CK
#define	R_SPIO          	0x08000a18	// 08000a18, wbregs names: SPIO
// SYSCLK Clock Counter (measures clock speed)
#define	R_TXCLK         	0x08000a1c	// 08000a1c, wbregs names: TXCLK
#define	R_VERSION       	0x08000a20	// 08000a20, wbregs names: VERSION
// FPGA CONFIG REGISTERS: 0x4e0-0x4ff
#define	R_CFG_CRC       	0x08000b00	// 08000b00, wbregs names: FPGACRC
#define	R_CFG_FAR       	0x08000b04	// 08000b00, wbregs names: FPGAFAR
#define	R_CFG_FDRI      	0x08000b08	// 08000b00, wbregs names: FPGAFDRI
#define	R_CFG_FDRO      	0x08000b0c	// 08000b00, wbregs names: FPGAFDRO
#define	R_CFG_CMD       	0x08000b10	// 08000b00, wbregs names: FPGACMD
#define	R_CFG_CTL0      	0x08000b14	// 08000b00, wbregs names: FPGACTL0
#define	R_CFG_MASK      	0x08000b18	// 08000b00, wbregs names: FPGAMASK
#define	R_CFG_STAT      	0x08000b1c	// 08000b00, wbregs names: FPGASTAT
#define	R_CFG_LOUT      	0x08000b20	// 08000b00, wbregs names: FPGALOUT
#define	R_CFG_COR0      	0x08000b24	// 08000b00, wbregs names: FPGACOR0
#define	R_CFG_MFWR      	0x08000b28	// 08000b00, wbregs names: FPGAMFWR
#define	R_CFG_CBC       	0x08000b2c	// 08000b00, wbregs names: FPGACBC
#define	R_CFG_IDCODE    	0x08000b30	// 08000b00, wbregs names: FPGAIDCODE
#define	R_CFG_AXSS      	0x08000b34	// 08000b00, wbregs names: FPGAAXSS
#define	R_CFG_COR1      	0x08000b38	// 08000b00, wbregs names: FPGACOR1
#define	R_CFG_WBSTAR    	0x08000b40	// 08000b00, wbregs names: WBSTAR
#define	R_CFG_TIMER     	0x08000b44	// 08000b00, wbregs names: CFGTIMER
#define	R_CFG_BOOTSTS   	0x08000b58	// 08000b00, wbregs names: BOOTSTS
#define	R_CFG_CTL1      	0x08000b60	// 08000b00, wbregs names: FPGACTL1
#define	R_CFG_BSPI      	0x08000b7c	// 08000b00, wbregs names: FPGABSPI
// Meganet register definitions
#define	R_ETH0_RXCMD    	0x08000c00	// 08000c00, wbregs names: ETH0RX
#define	R_ETH0_TXCMD    	0x08000c04	// 08000c00, wbregs names: ETH0TX
#define	R_ETH0_MACHI    	0x08000c08	// 08000c00, wbregs names: ETH0MACHI
#define	R_ETH0_MACLO    	0x08000c0c	// 08000c00, wbregs names: ETH0MACLO
#define	R_ETH0_IPADDR   	0x08000c10	// 08000c00, wbregs names: ETH0IPADDR, ETH0IP
#define	R_ETH0_RXMISS   	0x08000c14	// 08000c00, wbregs names: ETH0MISS
#define	R_ETH0_RXERR    	0x08000c18	// 08000c00, wbregs names: ETH0ERR
#define	R_ETH0_RXCRC    	0x08000c1c	// 08000c00, wbregs names: ETH0CRCER
#define	R_ETH0_DBGSEL   	0x08000c20	// 08000c00, wbregs names: ETH0DBGSL
#define	R_ETH0_RXPKTS   	0x08000c20	// 08000c00, wbregs names: ETH0RXPKT
#define	R_ETH0_ARPRX    	0x08000c24	// 08000c00, wbregs names: ETH0ARPRX
#define	R_ETH0_ICMPRX   	0x08000c28	// 08000c00, wbregs names: ETH0ICMRX
#define	R_ETH0_TXPKTS   	0x08000c2c	// 08000c00, wbregs names: ETH0TXPKT
#define	R_ETH0_ARPTX    	0x08000c30	// 08000c00, wbregs names: ETH0ARPTX
#define	R_ETH0_ICMPTX   	0x08000c34	// 08000c00, wbregs names: ETH0ICMTX
#define	R_ETH0_DATATX   	0x08000c38	// 08000c00, wbregs names: ETH0DATTX
#define	R_ETH0_TXABORTS 	0x08000c3c	// 08000c00, wbregs names: ETH0ABRTS
#define	R_ETH0_DBGRX    	0x08000c40	// 08000c00, wbregs names: ETH0DBGRX
#define	R_ETH0_DBGTX    	0x08000c44	// 08000c00, wbregs names: ETH0DBGTX
// Ethernet configuration (MDIO) port
#define	R_MDIO_BMCR     	0x08001000	// 08001000, wbregs names: BMCR
#define	R_MDIO_BMSR     	0x08001004	// 08001000, wbregs names: BMSR
#define	R_MDIO_PHYIDR1  	0x08001008	// 08001000, wbregs names: PHYIDR1
#define	R_MDIO_PHYIDR2  	0x0800100c	// 08001000, wbregs names: PHYIDR2
#define	R_MDIO_ANAR     	0x08001010	// 08001000, wbregs names: ANAR
#define	R_MDIO_ANLPAR   	0x08001014	// 08001000, wbregs names: ANLPAR
#define	R_MDIO_ANER     	0x08001018	// 08001000, wbregs names: ANER
#define	R_MDIO_ANNPTR   	0x0800101c	// 08001000, wbregs names: ANNPTR
#define	R_MDIO_ANNPRR   	0x08001020	// 08001000, wbregs names: ANNPRR
#define	R_MDIO_GBCR     	0x08001024	// 08001000, wbregs names: GBCR
#define	R_MDIO_GBSR     	0x08001028	// 08001000, wbregs names: GBSR
#define	R_MDIO_MACR     	0x08001034	// 08001000, wbregs names: MACR
#define	R_MDIO_MAADR    	0x08001038	// 08001000, wbregs names: MAADR
#define	R_MDIO_GBESR    	0x0800103c	// 08001000, wbregs names: GBESR
#define	R_MDIO_PHYCR    	0x08001040	// 08001000, wbregs names: PHYCR
#define	R_MDIO_PHYSR    	0x08001044	// 08001000, wbregs names: PHYSR
#define	R_MDIO_INER     	0x08001048	// 08001000, wbregs names: INER
#define	R_MDIO_INSR     	0x0800104c	// 08001000, wbregs names: INSR
#define	R_MDIO_RXERC    	0x08001060	// 08001000, wbregs names: RXERC
#define	R_MDIO_LDPSR    	0x0800106c	// 08001000, wbregs names: LDPSR
#define	R_MDIO_EPAGSR   	0x08001078	// 08001000, wbregs names: EPAGSR
#define	R_MDIO_PAGSEL   	0x0800107c	// 08001000, wbregs names: PAGSEL
#define	R_XMDIO_PC1R    	0x08001000	// 08001000, wbregs names: XPC1R
#define	R_XMDIO_PS1R    	0x08001004	// 08001000, wbregs names: XPS1R
#define	R_XMDIO_EEECR   	0x08001050	// 08001000, wbregs names: XEEECR
#define	R_XMDIO_EEEWER  	0x08001040	// 08001000, wbregs names: XEEEWER
#define	R_XMDIO_EEEAR   	0x080010f0	// 08001000, wbregs names: XEEEAR
#define	R_XMDIO_EEELPAR 	0x080010f4	// 08001000, wbregs names: XEEELPAR
#define	R_XMDIO_LACR    	0x08001068	// 08001000, wbregs names: XLACR
#define	R_XMDIO_LCR     	0x08001070	// 08001000, wbregs names: XLCR
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
#define	FLASHBASE	0x04000000
#define	FLASHLEN	0x04000000
#define	FLASHLGLEN	26
//
#define	FLASH_RDDELAY	1
#define	FLASH_NDUMMY	7
//
#define	BKRAMBASE	0x0a000000
#define	BKRAMLEN	0x00040000
#define	SDRAMBASE	0x40000000
#define	SDRAMLEN	0x40000000
// @REGDEFS.H.DEFNS at the top level
// End of definitions from REGDEFS.H.DEFNS
//
// The @REGDEFS.H.INSERT tag
//
// @REGDEFS.H.INSERT for masters
// @REGDEFS.H.INSERT for peripherals
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
#define	RESET_ADDRESS	0x04c00000
#else
#define	RESET_ADDRESS	0x0a000000
#endif	// FLASH_ACCESS
#endif	// BKROM_ACCESS
// }}}
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
