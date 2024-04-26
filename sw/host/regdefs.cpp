////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./regdefs.cpp
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga -I / -d -o . allclocks.txt clkcheck.txt global.txt crossbus.txt icape.txt version.txt pic.txt pwrcount.txt rtccount.txt spio.txt exconsole.txt wbuuart.txt wbuarbiter.txt bkram.txt flash.txt flashcfg.txt zipmaster.txt mdio.txt meganet.txt protocols.txt eth0bus.txt sdio.txt flashscope.txt mem_flash_bkram.txt mem_bkram_only.txt xdc.txt noddr.txt
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
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include <ctype.h>
#include "regdefs.h"

const	REGNAME	raw_bregs[] = {
	{ R_SDIO_CTRL     ,	"SDCARD"     	},
	{ R_SDIO_DATA     ,	"SDDATA"     	},
	{ R_SDIO_FIFOA    ,	"SDFIFOA"    	},
	{ R_SDIO_FIFOA    ,	"SDFIF0"     	},
	{ R_SDIO_FIFOA    ,	"SDFIFA"     	},
	{ R_SDIO_FIFOB    ,	"SDFIFOB"    	},
	{ R_SDIO_FIFOB    ,	"SDFIF1"     	},
	{ R_SDIO_FIFOB    ,	"SDFIFB"     	},
	{ R_SDIO_PHY      ,	"SDPHY"      	},
	{ R_FLASH         ,	"FLASH"      	},
	{ R_FLASHCFG      ,	"FLASHCFG"   	},
	{ R_FLASHCFG      ,	"QSPIC"      	},
	{ R_FLASHSCOPE    ,	"FLASHSCOPE" 	},
	{ R_FLASHSCOPED   ,	"FLASHSCOPED"	},
	{ R_CONSOLE_FIFO  ,	"UFIFO"      	},
	{ R_CONSOLE_UARTRX,	"RX"         	},
	{ R_CONSOLE_UARTRX,	"RXUART"     	},
	{ R_CONSOLE_UARTTX,	"TX"         	},
	{ R_CONSOLE_UARTTX,	"TXUART"     	},
	{ R_ADCCLK        ,	"ADCCLK"     	},
	{ R_BUILDTIME     ,	"BUILDTIME"  	},
	{ R_PIC           ,	"PIC"        	},
	{ R_PWRCOUNT      ,	"PWRCOUNT"   	},
	{ R_RTCCOUNT      ,	"RTCCOUNT"   	},
	{ R_RXETH0CK      ,	"RXETH0CK"   	},
	{ R_SPIO          ,	"SPIO"       	},
	{ R_TXCLK         ,	"TXCLK"      	},
	{ R_VERSION       ,	"VERSION"    	},
	{ R_CFG_CRC       ,	"FPGACRC"    	},
	{ R_CFG_FAR       ,	"FPGAFAR"    	},
	{ R_CFG_FDRI      ,	"FPGAFDRI"   	},
	{ R_CFG_FDRO      ,	"FPGAFDRO"   	},
	{ R_CFG_CMD       ,	"FPGACMD"    	},
	{ R_CFG_CTL0      ,	"FPGACTL0"   	},
	{ R_CFG_MASK      ,	"FPGAMASK"   	},
	{ R_CFG_STAT      ,	"FPGASTAT"   	},
	{ R_CFG_LOUT      ,	"FPGALOUT"   	},
	{ R_CFG_COR0      ,	"FPGACOR0"   	},
	{ R_CFG_MFWR      ,	"FPGAMFWR"   	},
	{ R_CFG_CBC       ,	"FPGACBC"    	},
	{ R_CFG_IDCODE    ,	"FPGAIDCODE" 	},
	{ R_CFG_AXSS      ,	"FPGAAXSS"   	},
	{ R_CFG_COR1      ,	"FPGACOR1"   	},
	{ R_CFG_WBSTAR    ,	"WBSTAR"     	},
	{ R_CFG_TIMER     ,	"CFGTIMER"   	},
	{ R_CFG_BOOTSTS   ,	"BOOTSTS"    	},
	{ R_CFG_CTL1      ,	"FPGACTL1"   	},
	{ R_CFG_BSPI      ,	"FPGABSPI"   	},
	{ R_ETH0_RXCMD    ,	"ETH0RX"     	},
	{ R_ETH0_TXCMD    ,	"ETH0TX"     	},
	{ R_ETH0_MACHI    ,	"ETH0MACHI"  	},
	{ R_ETH0_MACLO    ,	"ETH0MACLO"  	},
	{ R_ETH0_IPADDR   ,	"ETH0IPADDR" 	},
	{ R_ETH0_IPADDR   ,	"ETH0IP"     	},
	{ R_ETH0_RXMISS   ,	"ETH0MISS"   	},
	{ R_ETH0_RXERR    ,	"ETH0ERR"    	},
	{ R_ETH0_RXCRC    ,	"ETH0CRCER"  	},
	{ R_ETH0_DBGSEL   ,	"ETH0DBGSL"  	},
	{ R_ETH0_RXPKTS   ,	"ETH0RXPKT"  	},
	{ R_ETH0_ARPRX    ,	"ETH0ARPRX"  	},
	{ R_ETH0_ICMPRX   ,	"ETH0ICMRX"  	},
	{ R_ETH0_TXPKTS   ,	"ETH0TXPKT"  	},
	{ R_ETH0_ARPTX    ,	"ETH0ARPTX"  	},
	{ R_ETH0_ICMPTX   ,	"ETH0ICMTX"  	},
	{ R_ETH0_DATATX   ,	"ETH0DATTX"  	},
	{ R_ETH0_TXABORTS ,	"ETH0ABRTS"  	},
	{ R_ETH0_DBGRX    ,	"ETH0DBGRX"  	},
	{ R_ETH0_DBGTX    ,	"ETH0DBGTX"  	},
	{ R_MDIO_BMCR     ,	"BMCR"       	},
	{ R_MDIO_BMSR     ,	"BMSR"       	},
	{ R_MDIO_PHYIDR1  ,	"PHYIDR1"    	},
	{ R_MDIO_PHYIDR2  ,	"PHYIDR2"    	},
	{ R_MDIO_ANAR     ,	"ANAR"       	},
	{ R_MDIO_ANLPAR   ,	"ANLPAR"     	},
	{ R_MDIO_ANER     ,	"ANER"       	},
	{ R_MDIO_ANNPTR   ,	"ANNPTR"     	},
	{ R_MDIO_ANNPRR   ,	"ANNPRR"     	},
	{ R_MDIO_GBCR     ,	"GBCR"       	},
	{ R_MDIO_GBSR     ,	"GBSR"       	},
	{ R_MDIO_MACR     ,	"MACR"       	},
	{ R_MDIO_MAADR    ,	"MAADR"      	},
	{ R_MDIO_GBESR    ,	"GBESR"      	},
	{ R_MDIO_PHYCR    ,	"PHYCR"      	},
	{ R_MDIO_PHYSR    ,	"PHYSR"      	},
	{ R_MDIO_INER     ,	"INER"       	},
	{ R_MDIO_INSR     ,	"INSR"       	},
	{ R_MDIO_RXERC    ,	"RXERC"      	},
	{ R_MDIO_LDPSR    ,	"LDPSR"      	},
	{ R_MDIO_EPAGSR   ,	"EPAGSR"     	},
	{ R_MDIO_PAGSEL   ,	"PAGSEL"     	},
	{ R_XMDIO_PC1R    ,	"XPC1R"      	},
	{ R_XMDIO_PS1R    ,	"XPS1R"      	},
	{ R_XMDIO_EEECR   ,	"XEEECR"     	},
	{ R_XMDIO_EEEWER  ,	"XEEEWER"    	},
	{ R_XMDIO_EEEAR   ,	"XEEEAR"     	},
	{ R_XMDIO_EEELPAR ,	"XEEELPAR"   	},
	{ R_XMDIO_LACR    ,	"XLACR"      	},
	{ R_XMDIO_LCR     ,	"XLCR"       	},
	{ R_BKRAM         ,	"RAM"        	},
	{ R_ZIPCTRL       ,	"CPU"        	},
	{ R_ZIPCTRL       ,	"ZIPCTRL"    	},
	{ R_ZIPREGS       ,	"ZIPREGS"    	},
	{ R_ZIPS0         ,	"SR0"        	},
	{ R_ZIPS1         ,	"SR1"        	},
	{ R_ZIPS2         ,	"SR2"        	},
	{ R_ZIPS3         ,	"SR3"        	},
	{ R_ZIPS4         ,	"SR4"        	},
	{ R_ZIPS5         ,	"SR5"        	},
	{ R_ZIPS6         ,	"SR6"        	},
	{ R_ZIPS7         ,	"SR7"        	},
	{ R_ZIPS8         ,	"SR8"        	},
	{ R_ZIPS9         ,	"SR9"        	},
	{ R_ZIPS10        ,	"SR10"       	},
	{ R_ZIPS11        ,	"SR11"       	},
	{ R_ZIPS12        ,	"SR12"       	},
	{ R_ZIPSSP        ,	"SSP"        	},
	{ R_ZIPSSP        ,	"SR13"       	},
	{ R_ZIPCC         ,	"ZIPCC"      	},
	{ R_ZIPCC         ,	"CC"         	},
	{ R_ZIPCC         ,	"SCC"        	},
	{ R_ZIPCC         ,	"SR14"       	},
	{ R_ZIPPC         ,	"ZIPPC"      	},
	{ R_ZIPPC         ,	"PC"         	},
	{ R_ZIPPC         ,	"SPC"        	},
	{ R_ZIPPC         ,	"SR15"       	},
	{ R_ZIPUSER       ,	"ZIPUSER"    	},
	{ R_ZIPU0         ,	"UR0"        	},
	{ R_ZIPU1         ,	"UR1"        	},
	{ R_ZIPU2         ,	"UR2"        	},
	{ R_ZIPU3         ,	"UR3"        	},
	{ R_ZIPU4         ,	"UR4"        	},
	{ R_ZIPU5         ,	"UR5"        	},
	{ R_ZIPU6         ,	"UR6"        	},
	{ R_ZIPU7         ,	"UR7"        	},
	{ R_ZIPU8         ,	"UR8"        	},
	{ R_ZIPU9         ,	"UR9"        	},
	{ R_ZIPU10        ,	"SR10"       	},
	{ R_ZIPU11        ,	"SR11"       	},
	{ R_ZIPU12        ,	"SR12"       	},
	{ R_ZIPUSP        ,	"USP"        	},
	{ R_ZIPUSP        ,	"UR13"       	},
	{ R_ZIPUCC        ,	"ZIPUCC"     	},
	{ R_ZIPUCC        ,	"UCC"        	},
	{ R_ZIPUPC        ,	"ZIPUPC"     	},
	{ R_ZIPUPC        ,	"UPC"        	},
	{ R_ZIPSYSTEM     ,	"ZIPSYSTEM"  	},
	{ R_ZIPSYSTEM     ,	"ZIPSYS"     	}
};

// REGSDEFS.CPP.INSERT for any bus masters
// And then from the peripherals
// And finally any master REGS.CPP.INSERT tags
#define	RAW_NREGS	(sizeof(raw_bregs)/sizeof(bregs[0]))

const	REGNAME		*bregs = raw_bregs;
const	int	NREGS = RAW_NREGS;

unsigned	addrdecode(const char *v) {
	if (isalpha(v[0])) {
		for(int i=0; i<NREGS; i++)
			if (strcasecmp(v, bregs[i].m_name)==0)
				return bregs[i].m_addr;
		fprintf(stderr, "Unknown register: %s\n", v);
		exit(-2);
	} else
		return strtoul(v, NULL, 0);
}

const	char *addrname(const unsigned v) {
	for(int i=0; i<NREGS; i++)
		if (bregs[i].m_addr == v)
			return bregs[i].m_name;
	return NULL;
}

