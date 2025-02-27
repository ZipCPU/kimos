////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/ramscope.cpp
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	
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
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "design.h"
#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_RAMSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an SDIO scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_RAMSCOPE
#define	WBSCOPEDATA	R_RAMSCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	RAMSCOPE : public SCOPE {
public:
	RAMSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~RAMSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		// int	scl, sda;

		// scl = (val >> 13) & 1;
		// sda = (val >> 12) & 1;
		// printf("%3s %3s", (scl) ? "SCL":"", (sda) ? "SDA":"");
	}

	virtual	void	define_traces(void) {
		register_trace("alu_pc_valid",1,20);
		register_trace("alu_valid",   1,19);
		//
		register_trace("mem_ce",      1,18);
		register_trace("mem_busy",    1,17);
		register_trace("mem_rdbusy",  1,16);
		register_trace("mem_valid",   1,15);
		//
		register_trace("zip_cyc",    1,14);
		register_trace("zip_stb",    1,13);
		register_trace("zip_we",     1,12);
		register_trace("zip_stall",  1,11);
		register_trace("zip_ack",    1,10);
		//
		register_trace("sdram_cyc",  1, 9);
		register_trace("sdram_stb",  1, 8);
		register_trace("sdram_we",   1, 7);
		register_trace("sdram_stall",1, 6);
		register_trace("sdram_ack",  1, 5);
		//
		register_trace("dma_cyc",    1, 4);
		register_trace("dma_stb",    1, 3);
		register_trace("dma_we",     1, 2);
		register_trace("dma_stall",  1, 1);
		register_trace("dma_ack",    1, 0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	RAMSCOPE *scope = new RAMSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("ramscope.vcd");
	}
	delete	m_fpga;
}
#endif
