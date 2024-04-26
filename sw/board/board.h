////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./board.h
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
#ifndef	BOARD_H
#define	BOARD_H

// And, so that we can know what is and isn't defined
// from within our main.v file, let's include:
#include <design.h>

#ifndef	UDP_DBGPORT
#define	UDP_DBGPORT	5929
#define	UDP_DATAPORT	5930
#endif


////////////////////////////////////////////////////////////////////////////////
//
// ZipCPU defines and macros
// {{{
#include <design.h>

#define	_HAVE_ZIPSYS
#define	PIC	_zip->z_pic

#ifdef	INCLUDE_ZIPCPU
#ifdef INCLUDE_DMA_CONTROLLER
#define	_HAVE_ZIPSYS_DMA
#endif	// INCLUDE_DMA_CONTROLLER
#ifdef INCLUDE_ACCOUNTING_COUNTERS
#define	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
#endif	// INCLUDE_ACCOUNTING_COUNTERS
#endif // INCLUDE_ZIPCPU
// }}}


#define	SPIO_BTN0	0x0010000
#define	SPIO_BTN1	0x0020000


// Offsets for the ICAPE2 interface
#define	CFG_CRC		0
#define	CFG_FAR		1
#define	CFG_FDRI	2
#define	CFG_FDRO	3
#define	CFG_CMD		4
#define	CFG_CTL0	5
#define	CFG_MASK	6
#define	CFG_STAT	7
#define	CFG_LOUT	8
#define	CFG_COR0	9
#define	CFG_MFWR	10
#define	CFG_CBC		11
#define	CFG_IDCODE	12
#define	CFG_AXSS	13
#define	CFG_COR1	14
#define	CFG_WBSTAR	16
#define	CFG_TIMER	17
#define	CFG_BOOTSTS	22
#define	CFG_CTL1	24
#define	CFG_BSPI	31


// Network stream/packet interface
// {{{
#ifndef	ENETSTREAM_H
#define	ENETSTREAM_H
typedef struct ENETSTREAM_S {
        unsigned        n_rxcmd, n_txcmd;
        unsigned long   n_mac;
	unsigned	n_ipaddr;
        unsigned        n_rxmiss, n_rxerr, n_rxcrc;
} ENETSTREAM;
#endif
// }}}


//
// The Ethernet MDIO interface
//
#define MDIO_CONTROL	0x00
#define MDIO_STATUS	0x01
#define MDIO_PHYIDR1	0x02	// PHY ID Register #1
#define MDIO_PHYIDR2	0x03	// PHY ID Register #2
#define MDIO_ANAR	0x04	// Autonegotiation advertisement
#define MDIO_ANLPAR	0x05	// Autonegotiation link partner ability
#define MDIO_ANER	0x06	// Autonegotiation expansion
#define MDIO_ANNPTR	0x07	// Autonegotiation next page
#define MDIO_ANNPRR	0x08	// Autonegotiation link partner next page
#define MDIO_GBCR	0x09	// 1GBase-T Control
#define MDIO_GBSR	0x0a	// 1GBase-T Status
#define MDIO_MACR	0x0d	// MMD Access control
#define MDIO_MAADR	0x0e	// MMD Access register/data
#define MDIO_GBESR	0x0f	// Extended status
#define MDIO_LOOPBACK	0x11	// Vendor specific: remote loopback
#define MDIO_CBLDIAG	0x12	// Vendor specific: link MD cable diagnostic
#define MDIO_PMASTAT	0x13	// Vendor specific: Digital PMA/PCS status
#define MDIO_RXERCNT	0x15	// Vendor specific: RXER Counter
#define MDIO_INT	0x1b	// Vendor specific: Interrupt control/status
#define MDIO_AUTOMDIl	0x1b	// Vendor specific: Auto MDI/MDI-X
#define MDIO_PHYCTRL	0x1f	// Vendor specific: PHY control

#define XMDIO_PC1R	0x00
#define XMDIO_PS1R	0x01
#define XMDIO_EEECR	0x14
#define XMDIO_EEEWER	0x10
// #define XMDIO_EEEAR	0x
// #define XMDIO_EEELPAR	0x18
#define XMDIO_LACR	0x1a
#define XMDIO_LCR	0x1c
// #define XMDIO_ACCR	0x1b

typedef struct ENETMDIO_S {
	unsigned	e_v[32][32];
} ENETMDIO;



////////////////////////////////////////////////////////////////////////////////
//
// SDIO SD Card constants
// {{{
////////////////////////////////////////////////////////////////////////////////
//
//

// These will be defined in sdiodrv.h for the SDIO controller
struct SDIO_S;
// }}}


#define BUSPIC(X) (1<<X)


#define	SYSPIC(A)	(1<<(A))


typedef struct  CONSOLE_S {
	unsigned	u_setup;
	unsigned	u_fifo;
	unsigned	u_rx, u_tx;
} CONSOLE;

#define	_uart_txbusy	((_uart->u_fifo & 0x10000)==0)
#define	_uart_txidle	((_uart->u_tx   & 0x100)  ==0)


#define	ALTPIC(A)	(1<<(A))


#ifndef	WBSCOPE_H
#define	WBSCOPE_H

#define	WBSCOPE_NO_RESET	0x80000000u
#define	WBSCOPE_STOPPED		0x40000000u
#define	WBSCOPE_TRIGGERED	0x20000000u
#define	WBSCOPE_PRIMED		0x10000000u
#define	WBSCOPE_TRIGGER		(WBSCOPE_NO_RESET|0x08000000u)
#define	WBSCOPE_MANUAL		(WBSCOPE_TRIGGER)
#define	WBSCOPE_DISABLE		0x04000000u

typedef	struct	WBSCOPE_S {
	unsigned s_ctrl, s_data;
} WBSCOPE;
#endif


#ifdef	SPIO_ACCESS
#define	_BOARD_HAS_SPIO
static volatile unsigned *const _spio = ((unsigned *)0x08000a18);
#endif	// SPIO_ACCESS
#ifdef	PWRCOUNT_ACCESS
static volatile unsigned *const _pwrcount = ((unsigned *)0x08000a0c);
#endif	// PWRCOUNT_ACCESS
#ifdef	CFG_ACCESS
#define	_BOARD_HAS_ICAPTETWO
static volatile unsigned *const _icape = ((unsigned *)0x00000c00);
#endif	// CFG_ACCESS
#ifdef	VERSION_ACCESS
#define	_BOARD_HAS_VERSION
static volatile unsigned *const _version = ((unsigned *)0x08000a20);
#endif	// VERSION_ACCESS
#ifdef	ETH0_ACCESS
#define	_BOARD_HAS_ETH0
static volatile ENETSTREAM *const io_eth0 = ((ENETSTREAM *)0x08000e00);
#endif	// ETH0_ACCESS
#ifdef	TXCLK
static volatile unsigned *const _txclk = ((unsigned *)0x08000a1c);
#endif	// TXCLK
#define	_BOARD_HAS_BUILDTIME
static volatile unsigned *const _buildtime = ((unsigned *)0x08000a04);
#ifdef	NETCTRL_ACCESS
#define	_BOARD_HAS_NETMDIO
static volatile ENETMDIO *const _mdio = ((ENETMDIO *)0x08001000);
#endif	// NETCTRL_ACCESS
#ifdef	RXETH0CK
static volatile unsigned *const _rxeth0ck = ((unsigned *)0x08000a14);
#endif	// RXETH0CK
#ifdef	ADCCLK
static volatile unsigned *const _adcclk = ((unsigned *)0x08000a00);
#endif	// ADCCLK
#ifdef	FLASH_ACCESS
#define	_BOARD_HAS_FLASH
extern int _flash[1];
#endif	// FLASH_ACCESS
#ifdef	BKRAM_ACCESS
#define	_BOARD_HAS_BKRAM
extern char	_bkram[0x00040000];
#endif	// BKRAM_ACCESS
#ifdef	FLASHCFG_ACCESS
#define	_BOARD_HAS_FLASHCFG
static volatile unsigned * const _flashcfg = ((unsigned *)(0x08000400));
#endif	// FLASHCFG_ACCESS
#ifdef	SDIO_ACCESS
#define	_BOARD_HAS_SDIO
static volatile struct SDIO_S *const _sdio = ((struct SDIO_S *)0x02000000);
#endif	// SDIO_ACCESS
#ifdef	BUSPIC_ACCESS
#define	_BOARD_HAS_BUSPIC
static volatile unsigned *const _buspic = ((unsigned *)0x08000a08);
#endif	// BUSPIC_ACCESS
#ifdef	BUSCONSOLE_ACCESS
#define	_BOARD_HAS_BUSCONSOLE
static volatile CONSOLE *const _uart = ((CONSOLE *)0x08000800);
#endif	// BUSCONSOLE_ACCESS
#ifdef	FLASHSCOPE_SCOPC
#define	_BOARD_HAS_FLASHSCOPE
static volatile WBSCOPE *const _flashdbg = ((WBSCOPE *)0x08000600);
#endif	// FLASHSCOPE_SCOPC
//
// Interrupt assignments (3 PICs)
//
// PIC: buspic
#define	BUSPIC_SPIO	BUSPIC(0)
#define	BUSPIC_FLASHDBG	BUSPIC(1)
// PIC: syspic
#define	SYSPIC_DMAC	SYSPIC(0)
#define	SYSPIC_JIFFIES	SYSPIC(1)
#define	SYSPIC_TMC	SYSPIC(2)
#define	SYSPIC_TMB	SYSPIC(3)
#define	SYSPIC_TMA	SYSPIC(4)
#define	SYSPIC_ALT	SYSPIC(5)
#define	SYSPIC_BUS	SYSPIC(6)
#define	SYSPIC_SDCARD	SYSPIC(7)
#define	SYSPIC_UARTRXF	SYSPIC(8)
#define	SYSPIC_UARTTXF	SYSPIC(9)
// PIC: altpic
#define	ALTPIC_UIC	ALTPIC(0)
#define	ALTPIC_UOC	ALTPIC(1)
#define	ALTPIC_UPC	ALTPIC(2)
#define	ALTPIC_UTC	ALTPIC(3)
#define	ALTPIC_MIC	ALTPIC(4)
#define	ALTPIC_MOC	ALTPIC(5)
#define	ALTPIC_MPC	ALTPIC(6)
#define	ALTPIC_MTC	ALTPIC(7)
#define	ALTPIC_UARTTX	ALTPIC(8)
#define	ALTPIC_UARTRX	ALTPIC(9)
#endif	// BOARD_H
