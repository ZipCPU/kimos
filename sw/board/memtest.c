////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/memtest.c
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	Used to determine if the DDR3 SDRAM controller is working or
//		not.  Contains a series of tests, applied across memory, for
//	this purpose.
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
// }}}
#include <string.h>
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"
#include "txfns.h"

extern	char	_sdram[0x40000000];

#define	SCOPE_DELAY	16

#define	STEP(F,T)  asm volatile("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(F) : "r"(T))
#define	FAIL		asm("TRAP")

#ifdef	_BOARD_HAS_RAMSCOPE
#define	SET_SCOPE	_ramscope->s_ctrl = WBSCOPE_DISABLE | SCOPE_DELAY
#define	TRIGGER_SCOPE	_ramscope->s_ctrl = WBSCOPE_TRIGGER | SCOPE_DELAY
#else
#define	SET_SCOPE
#define	TRIGGER_SCOPE
#endif

#define	VERILATOR

//
// memchk
// {{{
unsigned	timestamps[12];

void	memchk(int *mem, int *end, unsigned seed) {
	int	counts = seed;
#ifdef	VERILATOR
	const	int	TAPS = 0x0002803;	//  16MB
#else
	// const	int	TAPS = 0x0005011;	//  32MB
	// const	int	TAPS = 0x000c009;	//  64MB
	// const	int	TAPS = 0x0018005;	// 128MB
	// const	int	TAPS = 0x0028081;	// 256
	// const	int	TAPS = 0x00485b5;	// 512MB
	// const	int	TAPS = 0x0110003;	// 2GB
	// const	int	TAPS = 0x0280005;	// 4GB
	const	int	TAPS = 0x0400015;	// 8GB (Previous)
	// const	int	TAPS = 0x0400019;	// 8GB
	// const	int	TAPS = 0x0400043;	// 8GB
	// const	int	TAPS = 0x0400051;	// 8GB
	// const	int	TAPS = 0x04000c1;	// 8GB
	// const	int	TAPS = 0x0400181;	// 8GB
	// const	int	TAPS = 0x0400501;	// 8GB
	// const	int	TAPS = 0x0401401;	// 8GB
	// const	int	TAPS = 0x07fffdf;	// 8GB
#endif
	char	*const cmem= (char *)mem;
	char	*const endc= (char *)end;
	unsigned	start, mid, stop, lnw;
	unsigned	ttim, ncyc, nbeat;
	volatile WBPERF	*const perf = _wbperf;

	for(int i=0; i<12; i++)
		timestamps[i] = 0;
	timestamps[0] = _zip->z_m.ac_ck;

	////////////////////////////////////////////////////////////////////////
	//
	// #1, data line check
	// {{{
	txchr('\n');
	for(int k=0; k<512; k++) {
		for(int j=0; j<512/8; j++) {
			if ((k>>3) == j)
				cmem[j] = (1<<(k&7));
			else
				cmem[j] = '\0';
		}

		CLEAR_DCACHE;

		for(int j=0; j<512/8; j++) {
			if ((k>>3) == j) {
				if (cmem[j] != (1<<(k&7)))
					FAIL;
			} else if (cmem[j] != '\0')
				FAIL;
		}
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Clear the bottom 3 LED's
	*_spio = 0x0e00;
	// }}}
#endif
	timestamps[1] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #2, address line check
	// {{{
	txchr('1');
	for(int k=0; cmem + (1<<k)<endc; k++) {
		for(int j=0; cmem + (1<<j) < endc; j++) {
			if (k == j)
				cmem[j] = 0xad;
			else
				cmem[j] = '\0';
		}

		CLEAR_DCACHE;

		for(int j=0; cmem + (1<<j) < endc; j++) {
			if (k == j) {
				if (cmem[j] != 0xad)
					FAIL;
			} else if (cmem[j] != '\0')
				FAIL;
		}
	}

#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Clear the bottom 3 LED's
	*_spio = 0x0e02;
	// }}}
#endif
	timestamps[2] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #3, sequential access, filled with LRS
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('2');
	if (1) {
		int	*mptr = mem;
		unsigned fill;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;

		start = _zip->z_m.ac_ck;

		// Write to memory
		// {{{
		// Verilator: 33 clocks / loop, all dominated by the SDRAM time
		// MIG:
		//	10ck/loop, 4 for the SDRAM
		//		or 17 on a MIG cache miss
		// UBER:
		//	15 clk/loop
		//	(All cache misses) ... 10 for access
		// UBER2:
		//	11 clk/loop, 6 for the SDRAM
		//	57 clks on a miss
		fill = (counts == 0) ? 1 : counts;
		while(mptr < end) {
			STEP(fill, TAPS);
			// fill = (fill&1)?((fill>>1)^TAPS):(fill>>1);
			*mptr++ = fill;
		}
		// }}}

		mid = _zip->z_m.ac_ck;
		perf->p_control = WBPERF_STOP;
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		CLEAR_DCACHE;
		// TRIGGER_SCOPE;	// CP #1

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;

		// Read and compare
		// {{{
		// Verilator: 17 clocks / loop, when in the cache
		// Verilator: 61 clocks / loop, cache miss, 39 for bus access
		//	47 for the memory controller (request to VALID)
		//	2,220 from cache request to cache request
		//		= 127*17 + 61*1
		// MIG:
		//	17 clocks when no cache miss
		//	61 clocks when cache miss
		// Uber:
		//	17 clocks when no cache miss
		//	43 clocks when cache miss
		fill = (counts == 0) ? 1 : counts;
		mptr = mem;
		while(mptr < end) {
			STEP(fill, TAPS);
			if (*mptr != (int)fill) {
				FAIL;
				break;
			}
			mptr++;
		}
		// }}}

		stop = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #2
		perf->p_control = WBPERF_STOP;

		// MIG:	0x0a187332:0x1157ffd9
		// MIG:	0x0a187343:0x1157ffd9 / 2^24
		//	10.096 : 17.344
		// MIG:	0x2861cb9f:0x356780BD / 2^26 (After FAIL; break; )
		//	10.096 : 13.351
		// Uber:
		//	0x0F7B0075:11349D81 / 2^24
		//	15.48 : 17.206
		// Uber2:
		//	0x0BA5DC0A:113AAA64 / 2^24
		//	11.648 : 17.229
		//	
		txstr("- SEQ: 0x"); txhex(mid-start); txstr(":"); txhex(stop-mid); txstr(" // ");


		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("--");
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;
		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("\n");
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// First test done, set the bottom LED
	*_spio = 0x0e04;
	// }}}
#endif
	timestamps[3] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #4, sequential access, read/write 3x at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('3');
	if (1) {
		int	*mptr = mem;
		unsigned fill;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;

		start = _zip->z_m.ac_ck;

		// Write to memory
		// {{{
		// VERILATOR: 35 clocks / loop
		// MIG:
		//	21 clocks / loop in cache
		//	21 clocks / loop when not in cache
		// Uber:
		//	21 clocks / loop
		//	41-42 clocks / loop ... on rare occasions
		// Uber2:
		//	21 clocks / loop, 8 clks/3SRAM accesses
		//	47,49,50,51 clocks / loop ... (every 38x, or 827ns)
		fill = counts + 4; if (fill == 0) fill = 1;
		while(mptr+3 < end) {
			register unsigned a, b, c;


			STEP(fill, TAPS);	a = fill;
			STEP(fill, TAPS);	b = fill;
			STEP(fill, TAPS);	c = fill;

			mptr[0] = a;
			mptr[1] = b;
			mptr[2] = c;

			mptr += 3;
		}
		// }}}

		mid = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #3
		CLEAR_DCACHE;

		perf->p_control = WBPERF_STOP;
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;


		// Read and compare
		// {{{
		// VERILATOR: 18 clocks / loop, when all is in the cache
		//	55 clocks / loop when not in the cache
		// 5 clocks per jump, 1 + 4 stalls
		// MIG:
		//	24 clocks in cache
		//	68-69 clocks when not in cache
		// Uber:
		//	24 clocks in cache
		//	50,51,59 clocks when not in cache
		// Uber2:
		//	24 clocks (in cache)
		//	50,51 clocks when not in cache
		//		(17 clocks for SDRAM cycle for 8 words)
		mptr = mem;
		fill = counts + 4; if (fill == 0) fill = 1;
		while(mptr+3 < end) {
			register unsigned a, b, c;

			a = mptr[0];
			b = mptr[1];
			c = mptr[2];

			STEP(fill, TAPS);
			if (a != (int)fill) {
				FAIL; break;
			}

			STEP(fill, TAPS);
			if (b != (int)fill) {
				FAIL; break;
			}

			STEP(fill, TAPS);
			if (c != (int)fill) {
				FAIL; break;
			}

			mptr+=3;
		}
		// }}}

		stop = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #4
		perf->p_control = WBPERF_STOP;

		// MIG:	0x06aaaaba:0x0c5d8e30 / (2^23/3)
		//	0x06aaaab8:0x0c5d8e2e / (2^23/3)
		//	0x06aaaab8:0x0c5d8e25 / (2^23/3)
		//	20 : 37.096
		// Uber:
		//	0x072CE9A7:08376DB0 / (2^24/3)
		//	21.526 : 24.65
		// Uber2:
		//	0x07411F82:08391744
		//	21.763 : 24.669
		txstr(" - TRW: 0x"); txhex(mid-start); txstr(":"); txhex(stop-mid); txstr(" // ");
		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("--");
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;
		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("\n");
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Second test done, set the LEDs to reflect that
	*_spio = 0x0e06;
	// }}}
#endif
	timestamps[4] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #5, sequential access, read/write 3x characters at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('4');
	if (1) {
		char	*mcptr;
		unsigned fill;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;

		start = _zip->z_m.ac_ck;

		// Write to memory
		// {{{
		// VERILATOR: 35 clocks per loop, all in memory access
		// MIG:
		//	20 clocks when in cache
		//	20 clocks when not in cache
		// Uber:
		//	20 clocks
		//	39 clocks on miss
		// Uber2:
		//	20 clocks
		//	47 clocks on a miss
		//		(8 clocks for 3 accesses)
		mcptr = (char *)mem;
		fill = counts + 19; if (fill == 0) fill = 1;
		while(mcptr+3 < endc) {
			register char a, b, c;

			STEP(fill, TAPS);	a = fill; // & 0x0ff;
			STEP(fill, TAPS);	b = fill; // & 0x0ff;
			STEP(fill, TAPS);	c = fill; // & 0x0ff;

			mcptr[0] = a;
			mcptr[1] = b;
			mcptr[2] = c;

			mcptr += 3;
		}
		// }}}

		mid = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #5
		CLEAR_DCACHE;

		perf->p_control = WBPERF_STOP;
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;


		// Read and compare
		// {{{
		// VERILATOR: 26 clocks / loop, when its all in the cache
		// VERILATOR: 70 clocks / loop, for cache miss
		//	37 for the SDRAM read
		// MIG:
		//	26 clocks / loop, when its all in the cache
		//	70 clocks / loop, for cache missess
		// Uber:
		//	26 clocks / loop, when its all in the cache
		//	52 clocks / loop, for cache missess
		// Uber2:
		//	26 clocks / loop, when its all in the cache
		//	52 clocks / loop, for cache missess
		//		17 SDRAM clocks to fill a cache line
		mcptr = (char *)mem;
		fill = counts + 19; if (fill == 0) fill = 1;
		while(mcptr+3 < endc) {
			register unsigned a, b, c;

			a = mcptr[0];
			b = mcptr[1];
			c = mcptr[2];

			STEP(fill, TAPS);
			a ^= fill;
			if ((a&0x0ff)!=0) {
				FAIL;
				break;
			}

			STEP(fill, TAPS);
			b ^= fill;
			if ((b &0x0ff)!=0) {
				FAIL;
				break;
			}

			STEP(fill, TAPS);
			c ^= fill;
			if ((c&0x0ff)!=0) {
				FAIL;
				break;
			}

			mcptr+=3;
		}
		// }}}
		stop = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #6
		perf->p_control = WBPERF_STOP;

		// MIG:	0x1aaaaabe:0x37076855
		//	0x1aaaaac4:0x3707686c
		//	0x1aaaaad6:0x3707686f / (2^26/3)
		//	-> 20 : 41.272
		// Uber:
		//	0x1B4D222B:22E1A9CF
		//	0x1B4D2244:22E1A9D9
		//	0x1B4D2249:22E1A9ED / (2^26/3)
		//	-> 20.476 : 26.161
		//	818 clocks between offline
		// Uber2:
		//	0x1B911132:22E39949
		//	-> 20.675 : 26.167
		//	827 clocks between offlines
		txstr(" - TRB: 0x"); txhex(mid-start); txstr(":"); txhex(stop-mid); txstr(" // ");

		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("--");
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;
		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("\n");
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Third test done
	*_spio = 0x0e08;
	// }}}
#endif
	timestamps[5] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #6, random access, read/write one word at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	txchr('5');
	if (1) {
		int	*mptr = mem;
		unsigned afill, dfill, amsk, initial_afill;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;

		start = _zip->z_m.ac_ck;

		// Write to memory
		// {{{
		// VERILATOR: 33 Counts / loop
		// MIG:
		//	19 counts / loop in the cache
		//	but ... no cache misses noted ???
		// Uber:
		//	19 counts / loop
		//	39,40 counts sometimes 
		// Uber2:
		//	19 counts / loop
		//	48 counts sometimes 
		afill = counts;       if (afill == 0) afill = 1;
		dfill = counts + 23;  if (dfill == 0) dfill = 1;
		initial_afill = afill;
		amsk  = (end-mem) - 1;
		do {
			STEP(afill, TAPS);
			STEP(dfill, TAPS);
			if ((afill&(~amsk)) == 0)
				mptr[afill&amsk] = dfill;
		} while(afill != initial_afill);
		// }}}

		mid = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #7
		CLEAR_DCACHE;

		perf->p_control = WBPERF_STOP;
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		perf->p_control = WBPERF_CLEAR;
		perf->p_control = WBPERF_START;


		// Read and compare
		// {{{
		// VERILATOR:	70 Clocks per loop (rarely in cache)
		// MIG:
		//	70 clocks / loop
		//	but ... some loops are 1 clock longer ??
		//	80 clocks if the MIG is slow
		// Uber:
		//	52,54 clocks / loop
		//	70,76 clocks / loop sometimes
		// Uber2:
		//	52,54 clocks / loop (52 when no stalls)
		//	79,81,83,85 clocks/loop every 827 clocks
		afill = counts;       if (afill == 0) afill = 1;
		dfill = counts + 23;  if (dfill == 0) dfill = 1;
		initial_afill = afill;
		do {
			STEP(afill, TAPS);
			STEP(dfill, TAPS);
			if ((afill & (~amsk)) == 0) {
				if (mptr[afill&amsk] != (int)dfill) {
					FAIL;
					break;
				}
			}
		} while(afill != initial_afill);
		// }}}

		stop = _zip->z_m.ac_ck;
		// TRIGGER_SCOPE;	// CP #8
		perf->p_control = WBPERF_STOP;

		// MIG:	0x0980000a:0x233c60de / 2^23
		// 	-> 19 : 70.472
		// Uber:
		//	0x09BCF4F1:1B43B86B
		//	-> 19.476 : 54.529
		// Uber2:
		//	0x09D8617A:1B90830E
		//	-> 19.69 : 55.129
		// Comparable write speed(s), 23% faster reads
		txstr(" - RNA: 0x"); txhex(mid-start); txstr(":"); txhex(stop-mid); txstr(" // ");

		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("--");
		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;
		txhex(ttim); txstr(":"); txhex(ncyc); txstr(":");
			txhex(nbeat); txstr("\n");
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Fourth test done
	*_spio = 0x0e0a;
	// }}}
#endif
	timestamps[6] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #7, memcpy
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('6');
	lnw = end-mem;
	start = _zip->z_m.ac_ck;
	// 3 writes per loop, 2-writes at a time: 24bytes/loop
	// MIG:
	//	55 cycle loops when in the cache
	//	71 cycles on a cache write miss
	//	87 cycles on a cache read miss
	// Uber:
	//	 79 cycles / loop, 4 writes / loop, 2 writes at a time (?!?!?)
	//	116 on a write miss
	//	109 on a cache read miss
	// Uber2:
	//	 63 clocks / loop when in the cache
	//	 93 cycles on a cache read miss
	//	102 cycles on a cache write miss (i.e. refresh clash)
	//   *NOTE*: These accesses likely break the UberDDR3's bank machine
	//	optimization(s), since both reads and writes will (likely)
	//	take place on the same bank.
	memcpy(mem+lnw/2, mem, lnw/2);
	stop = _zip->z_m.ac_ck;
	// TRIGGER_SCOPE;	// CP #9
	txstr(" - CPY: 0x"); txhex(stop-start); txstr("\n");
	// MIG		-> 0x00ed081c
	// Uber		-> 0x01517608
	// Uber2	-> 0x0110E8E9
	timestamps[7] = stop;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #8, memcmp
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('7');
	lnw = end-mem;
	start = _zip->z_m.ac_ck;
	// MIG:
	//	106 clocks per loop
	//	EVERYTHING is a cache miss
	//	139 clocks in a bad MIG day
	// Uber:
	//	 74 clocks / loop
	//	EVERYTHING is a cache miss
	//	 78 clocks / loop on a bad day
	// Uber2:
	//	 74 clocks / loop
	//	EVERYTHING is a cache miss
	//	 87 clocks / loop on a refresh clash
	//  *NOTE*: Because these accesses are power of two accesses,
	//	they (likely) break the UberDDR3's bank machines.
	if (0 != memcmp(mem+lnw/2, mem, lnw/2))
		FAIL;
	stop = _zip->z_m.ac_ck;
	// TRIGGER_SCOPE;	// CP #A
	txstr(" - CMP: 0x"); txhex(stop-start); txstr("\n");
	// MIG	->	0x06a799ae
	// Uber	->	0x04a5d1e2
	// Uber2 ->	0x04B2E90A
	timestamps[8] = stop;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #9, ZipDMA high speed extended throughput check, variable buffer size
	// {{{
	// VERILATOR: 102 clocks / loop / 16 words
#ifdef	_HAVE_ZIPSYS_DMA
	unsigned	ln = (endc - cmem)/2;
	char	*const	midc = &cmem[ln];

	for(int sz=1024; sz > 64; sz =  sz>>1) {
		// WRITES
		// {{{
		perf->p_control = WBPERF_CLEAR;
		_zip->z_dma.d_rd = cmem;
		_zip->z_dma.d_wr = midc;
		_zip->z_dma.d_len= ln;
		perf->p_control = WBPERF_START | 0x010;
		_zip->z_dma.d_ctrl = DMACCOPY | (sz & 1023);
		if (perf->p_control == 0)
			txstr("-- NO START\n");
		while(_zip->z_dma.d_ctrl & DMA_BUSY)
			;
		perf->p_control = WBPERF_STOP;

		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		txstr("\nWR : 0x"); txhex(ttim); txstr(" = (0x"); txhex(ncyc);
			txstr(" * L) + (0x"); txhex(nbeat); txstr(" * T)\n");
		// }}}

		// READS
		// {{{
		perf->p_control = WBPERF_CLEAR;
		_zip->z_dma.d_rd = cmem;
		_zip->z_dma.d_wr = midc;
		_zip->z_dma.d_len= ln;
		perf->p_control = WBPERF_START | 0x020;
		_zip->z_dma.d_ctrl = DMACCOPY | (sz & 1023);
		if (perf->p_control == 0)
			txstr("-- NO START\n");
		while(_zip->z_dma.d_ctrl & DMA_BUSY)
			;
		perf->p_control = WBPERF_STOP;

		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		txstr("RD : 0x"); txhex(ttim); txstr(" = (0x"); txhex(ncyc);
			txstr(" * L) + (0x"); txhex(nbeat); txstr(" * T)\n");
		// }}}

		// ALL
		// {{{
		perf->p_control = WBPERF_CLEAR;
		_zip->z_dma.d_rd = cmem;
		_zip->z_dma.d_wr = midc;
		_zip->z_dma.d_len= ln;
		perf->p_control = WBPERF_START;
		_zip->z_dma.d_ctrl = DMACCOPY | (sz & 1023);
		if (perf->p_control == 0)
			txstr("-- NO START\n");
		while(_zip->z_dma.d_ctrl & DMA_BUSY)
			;
		perf->p_control = WBPERF_STOP;
		TRIGGER_SCOPE;	// CP #B

		ttim = perf->p_stb + perf->p_stall + perf->p_simple_acks + perf->p_wait;
		nbeat = perf->p_stb;
		ncyc = perf->p_numcyc;

		txstr("ALL: 0x"); txhex(ttim); txstr(" = (0x"); txhex(ncyc);
			txstr(" * L) + (0x"); txhex(nbeat); txstr(" * T)\n");
		// }}}

		// MIG:
		//	Rough 79 cycles per loop, largest size
		// Uber:
		//	Rough 70 cycles per loop
		//	93,95,109 on a miss of some type
		//	WRITES:	27 clocks / 16 words (when no delays)
		//	READS:	27 clocks / 16 words
		// Uber2:
		//	 66 clocks per loop (roughly)
		//	101 if it hits during a refresh
	}

	perf->p_control = WBPERF_CLEAR;
#else
		txchr('x');
#endif
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Fourth test done

	// Toggle bit 0 (0x01) as well--since we just finished another
	// round.  This way the toggling bit will be the indication
	// that the memory controller has been successful.
	*_spio = ((*_spio&0x1)^0x1)|0x0f0c;
	// }}}
#endif
		timestamps[9] = _zip->z_m.ac_ck;
	// }}}
}
// }}}

// DMA Analysis notes:
// {{{
// MIG:
// 0x00211C38 = (0x00010000 * L) + (0x00100000 * T)
// 0x0030593D = (0x00020000 * L) + (0x00100000 * T)
// 0x004E6EE6 = (0x00040000 * L) + (0x00100000 * T)
//
// x = [ 0x0211c38 ; 0x030593d; 0x04e6ee6 ];
// A = [ 0x01000 0x0100000; 0x020000 0x0100000 ; 0x040000 0x0100000 ];
// A\x
//	11.5296, 1.8749
//	Latency = 11.5296 cycles, throughput = 53%
//	(Includes a 1 clock conversion from WB to AXI, so ...
//		Latency should be 10.53 cycles)
//
// Uber2:
// 0x001A7558 = (0x00010000 * L) + (0x00100000 * T)
// 0x0023C008 = (0x00020000 * L) + (0x00100000 * T)
// 0x00371CD7 = (0x00040000 * L) + (0x00100000 * T)
//
// x = [ 0x001a7558; 0x023c008; 0x0371cd7; 0x01a7558; 0x023c008; 0x037cd7];
// A = [ 0x01000 0x0100000; 0x020000 0x0100000 ; 0x040000 0x0100000 ];
// A\x
//	7.2902, 1.5234
//	Latency = 7.3 cycles, throughput = 65% (??)
// }}}

//
// runtest(void)
// {{{
void	runtest(void) {
	int	counts = 0;
	int	*const mem = (int *)_sdram;
	int	*const end = (int *)(&_sdram[sizeof(_sdram)]);
#ifdef	VERILATOR
	unsigned const BLKSIZE = (1u<<14);	// 16kB
#else
	// unsigned const BLKSIZE = (1u<<24);	// 16MB
	unsigned const BLKSIZE = (1u<<26);	// 64MB
#endif

	txstr("\n+------------------------------+\n"
		"|-        MEMORY TEST         -|\n"
		"+------------------------------+\n");
#ifdef	_BOARD_HAS_SPIO
	// Clear any/all LED's
	*_spio = 0x0ff00;
#endif

#ifdef	_BOARD_HAS_ZIPSCOPE
	_zipscope->s_ctrl = SCOPE_DELAY | WBSCOPE_MANUAL;
#endif

	while(1) {
		int	*run_start, *run_end;

		counts++;
		for(run_start = mem; run_start < end - BLKSIZE;	
					run_start = run_start + BLKSIZE) {
			run_end = run_start + BLKSIZE;
			memchk(run_start, run_end, counts);
		}
	}
}
// }}}

//
// main
// {{{
// Create and start a user task that can then be halted on any error
int	main(void) {
	unsigned zero = 0;
	unsigned	usp[512];

	asm("MOV %0,uR0" : : "r"(zero));
	asm(
	"\tMOV uR0,uR1\n"
	"\tMOV uR0,uR2\n"
	"\tMOV uR0,uR3\n"
	"\tMOV uR0,uR4\n"
	"\tMOV uR0,uR5\n"
	"\tMOV uR0,uR6\n"
	"\tMOV uR0,uR7\n"
	"\tMOV uR0,uR8\n"
	"\tMOV uR0,uR9\n"
	"\tMOV uR0,uR10\n"
	"\tMOV uR0,uR11\n"
	"\tMOV uR0,uR12\n"
	);

	SET_SCOPE;
#ifdef	_BOARD_HAS_ZIPSCOPE
	// Reset the scope on startup
	_zipscope->s_ctrl = SCOPE_DELAY;
#endif

	asm("MOV %0,uSP" : : "r"(&usp[511]));
	asm("MOV %0,uPC" : : "r"(runtest));

	zip_rtu();
#ifdef	_BOARD_HAS_ZIPSCOPE
	// If the scope hasn't (yet) triggered, trigger it now
	_zipscope->s_ctrl = SCOPE_DELAY | WBSCOPE_TRIGGER | WBSCOPE_MANUAL;
#endif
#ifdef	_BOARD_HAS_SPIO
	// Activate all LEDs
	*_spio = 0x0ffff;
#endif
	zip_halt();
}
// }}}

