////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/ddr3scope.cpp
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

#ifndef	R_DDR3SCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an DDR3 scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_DDR3SCOPE
#define	WBSCOPEDATA	R_DDR3SCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	DDR3SCOPE : public SCOPE {
	DEVBUS	*m_fpga;
public:
	DDR3SCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) { m_fpga = fpga; };
	~DDR3SCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		// int	scl, sda;

		// scl = (val >> 13) & 1;
		// sda = (val >> 12) & 1;
		// printf("%3s %3s", (scl) ? "SCL":"", (sda) ? "SDA":"");
	}

	virtual	void	define_traces(void) {
		// The DDR3 controller defines three sets of debugging wires
		unsigned	dbg_sel=0;

		dbg_sel = m_fpga->readio(R_DDR3_PHYDBGSEL) & 0x0f;

		switch(dbg_sel) {
		case 0:	// Calibration state
			// {{{
			// register_trace("o_phy_odelay_dqs_cntvaluein", 3,28);
			// register_trace("o_phy_idelay_dqs_cntvaluein", 5,23);
			register_trace("initial_dqs", 1,30);
			register_trace("dqs_target_index", 5,23);
			register_trace("o_phy_idelay_data_cntvaluein", 5,18);
			register_trace("o_phy_idelay_data_ld", 1,17);
			register_trace("o_phy_odelay_data_ld", 1,16);
			register_trace("o_phy_idelay_dqs_ld",  1,15);
			register_trace("o_phy_odelay_dqs_ld",  1,14);
			register_trace("dqs_start_index", 6,8);
			register_trace("lane", 3,5);
			register_trace("state_calibrate", 5,0);
			break;
			// }}}
		case 1: // Upper SERDES data
			// {{{
			register_trace("iserdes_dat",    30, 0);
			break;
			// }}}
		case 2: // Lower SERDES data
			// {{{
			register_trace("iserdes_dat",    30, 0);
			break;
			// }}}
		case 3: // Also calibration state
			// {{{
			register_trace("initial_dqs", 1,30);
			register_trace("i_phy_iserdes_dqs", 2,28);
			register_trace("dqs_start_index_repeat", 3,25);
			register_trace("o_phy_idelay_dqs_cntvaluein", 5,20);
			register_trace("dqs_target_index", 6,14);
			register_trace("dqs_start_index", 6,8);
			register_trace("lane", 3,5);
			register_trace("state_calibrate", 5,0);
			break;
			// }}}
		default:
			break;
		}
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	DDR3SCOPE *scope = new DDR3SCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("ddr3scope.vcd");
	}
	delete	m_fpga;
}
#endif
