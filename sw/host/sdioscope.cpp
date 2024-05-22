////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/sdioscope.cpp
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

#ifndef	R_SDIOSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an SDIO scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_SDIOSCOPE
#define	WBSCOPEDATA	R_SDIOSCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SDIOSCOPE : public SCOPE {
public:
	SDIOSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~SDIOSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		// int	scl, sda;

		// scl = (val >> 13) & 1;
		// sda = (val >> 12) & 1;
		// printf("%3s %3s", (scl) ? "SCL":"", (sda) ? "SDA":"");
	}

	virtual	void	define_traces(void) {
		// OPT_IO=0 => neither SERDES or DDR
		//	= 1	=> DDR, but not SERDES
		//	= 2	=> SERDES (not yet defined)
		//			(Bastardized for SDWB+DMA purposes)
		//	= 3	=> SDWB+DMA debugging
		const unsigned	OPT_IO=3;

		switch(OPT_IO) {
		case 0:
			// {{{
			register_trace("trigger",   1,31);
			register_trace("i_sdclk",   1,25);
			register_trace("i_cmd_en",  1,23);
			register_trace("i_cmd_data",1,22);
			register_trace("w_cmd",     1,20);
			register_trace("r_cmd_strb",1,19);
			register_trace("r_cmd",     1,18);
			register_trace("dat_en",    1,17);
			register_trace("rx_strb",   1,16);
			register_trace("rx_data",   8, 8);
			register_trace("io_dat",    8, 0);
			break;
			// }}}
		case 1:
			// {{{
			register_trace("trigger",   1,31);
			register_trace("i_rx_en",   1,28);
			register_trace("sample_ck", 2,26);
			register_trace("i_sdclk",   2,24);
			register_trace("i_cmd_en",  1,23);
			register_trace("i_cmd_data",2,21);
			register_trace("w_cmd",     1,20);
			register_trace("r_cmd_strb",1,19);
			register_trace("r_cmd",     1,18);
			register_trace("dat_en",    1,17);
			register_trace("rx_strb",   1,16);
			register_trace("rx_data",   8, 8);
			register_trace("io_dat",    8, 0);
			break;
			// }}}
		case 2:
			// {{{
			register_trace("trigger",   1,31);
			register_trace("i_rx_en",   1,28);
			register_trace("sample_ck", 2,26);
			register_trace("i_sdclk",   2,24);
			register_trace("i_cmd_en",  1,23);
			register_trace("i_cmd_data",2,21);
			register_trace("w_cmd",     1,20);
			register_trace("r_cmd_strb",1,19);
			register_trace("r_cmd",     1,18);
			register_trace("dat_en",    1,17);
			register_trace("rx_strb",   1,16);
			//
			// register_trace("r_tx",        1, 15);
			// register_trace("o_sd2s_valid",1, 14);
			// register_trace("i_sd2s_ready",1, 13);
			// register_trace("o_sd2s_last", 1, 12);
			register_trace("dma_stb",     1, 15);
			register_trace("dma_err",     1, 14);
			register_trace("i_dma_ack",   1, 13);
			register_trace("i_dma_err",   1, 12);
			// register_trace("dma_addr_hi", 2, 12);

			//
			register_trace("rx_data",   4, 8);
			//
			// register_trace("o_dma_sd2s",  1, 7);
			// register_trace("i_dma_busy",  1, 6);
			// register_trace("i_dma_err",   1, 5);
			// register_trace("r_dma_loaded",1, 4);

			register_trace("dma_addr",4, 4);
			// register_trace("subcount",4, 4);
			//
			register_trace("io_dat",    4, 0);
			break;
			// }}}
		case 3:
			register_trace("trigger",    1,31);
			register_trace("cmd_busy",   1,30);
			register_trace("mem_busy",   1,29);
			register_trace("dma_err",    1,28);
			register_trace("dma_abort",  1,27);
			register_trace("dma_stopped",1,26);
			register_trace("sd2s_valid", 1,25);
			register_trace("sd2s_ready", 1,24);
			register_trace("sd2s_last",  1,23);
			register_trace("o_dma_sd2s", 1,22);
			register_trace("i_dma_busy", 1,21);
			register_trace("i_dma_err",  1,20);
			register_trace("dma_fifo",   1,19);
			register_trace("dma_loaded", 2,17);
			register_trace("dma_busy",   1,16);
			//
			register_trace("dma_stb",    1,15);
			// register_trace("i_dma_stall",   1,14);
			register_trace("i_dma_err",  1,13);
			register_trace("i_dma_ack",  1,12);
			register_trace("o_dma_addr",12, 0);
			break;
		default:
			break;
		}
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SDIOSCOPE *scope = new SDIOSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("sdioscope.vcd");
	}
	delete	m_fpga;
}
#endif
