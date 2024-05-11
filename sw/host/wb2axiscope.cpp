////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/wb2axiscope.cpp
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	To read out, and decompose, the results of the wishbone scope
//		as applied to the WB2AXI converter found.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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

#include "port.h"
#include "regdefs.h"
#include "scopecls.h"
#include "devbus.h"

#if	defined(R_AXIDBG) && defined(R_AXIDBGD)
#define	WBSCOPE		R_AXIDBG
#define	WBSCOPEDATA	R_AXIDBGD
#else
#define	NO_SCOPE
#define	WBSCOPE	0
#define	WBSCOPEDATA	0
#endif

#include "zopcodes.h"

DEVBUS	*m_fpga;

class	WB2AXISCOPE : public SCOPE {
public:
	WB2AXISCOPE(DEVBUS *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, true, vecread) {};
	~WB2AXISCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
	}

	virtual	void	define_traces(void) {
		register_trace("i_reset",       1, 30);
		register_trace("o_sys_reset",   1, 29);
		//
		register_trace("empty",      1, 27);
		register_trace("flushing",   1, 26);
		register_trace("AWVALID",    1, 25);
		register_trace("WVALID",     1, 24);
		register_trace("AWREADY",    1, 23);
		register_trace("WREADY",     1, 22);
		register_trace("BVALID",     1, 21);
		register_trace("ARVALID",    1, 20);
		register_trace("ARREADY",    1, 19);
		register_trace("RVALID",     1, 18);
		register_trace("i_wb_cyc",   1, 17);
		register_trace("i_wb_stb",   1, 16);
		register_trace("i_wb_we",    1, 15);
		register_trace("o_wb_stall", 1, 14);
		register_trace("o_wb_ack",   1, 13);
		register_trace("o_wb_err",   1, 12);
		register_trace("npending",   9,  0);
	}
};

int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("Design was not built with a WB2AXI scope\n");
#else
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	FPGAOPEN(m_fpga);

	WB2AXISCOPE *scope = new WB2AXISCOPE(m_fpga, WBSCOPE, true);
	if (!scope->ready()) {
		// If we get here, then ... nothing started the scope.
		// It either hasn't primed, hasn't triggered, or hasn't finished
		// recording yet.  Trying to read data would do nothing but
		// read garbage, so we don't try.
		printf("Scope is not yet ready:\n");
		scope->decode_control();
		scope->decode(WBSCOPEDATA);
		printf("\n");
	} else {
		// The scope has been primed, triggered, the holdoff wait 
		// period has passed, and the scope has now stopped.
		//
		// Hence we can read from our scope the values we need.
		scope->print();
		// If we want, we can also write out a VCD file with the data
		// we just read.
		scope->writevcd("wb2axi.vcd");
	}

	// Now, we're all done.  Let's be nice to our interface and shut it
	// down gracefully, rather than letting the O/S do it in ... whatever
	// manner it chooses.
	delete	m_fpga;
#endif
}
