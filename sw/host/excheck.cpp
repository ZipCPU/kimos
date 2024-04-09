////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/excheck.cpp
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	A quick program to check whether or not the ExBus compression
//		works correctly as advertised.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
#include <stdint.h>

#include "regdefs.h"
#include "port.h"
#include "devbus.h"

typedef	DEVBUS FPGA;

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

bool	isvalue(const char *v) {
	const char *ptr = v;

	while(isspace(*ptr))
		ptr++;

	if ((*ptr == '+')||(*ptr == '-'))
		ptr++;
	if (*ptr == '+')
		ptr++;
	if (*ptr == '0') {
		ptr++;
		if (tolower(*ptr) == 'x')
			ptr++;
	}

	return (isdigit(*ptr));
}

int main(int argc, char **argv) {
	const	unsigned NLEN = 768;
	const char *host = FPGAHOST;
	int	port=FPGAPORT;
	int	opt;
	uint32_t	*testbuf, *checkbuf, *ovbuf;
	bool	passed = true;

	// Process all arguments, save the address and optional value
	// {{{
	while(-1 != (opt=getopt(argc, argv, "dn:p:m:"))) {
		switch(opt) {
		// case 'h': usage(); exit(EXIT_SUCCESS); break;
		case 'n': host = strdup(optarg); break;
		case 'p': port = strtoul(optarg, NULL, 0); break;
		default: // usage();
			exit(EXIT_FAILURE);
			break;
		}
	}
	// }}}

	{
		char	comstr[256];
		sprintf(comstr, "UART://%s:%d", host, port);
		m_fpga = connect_devbus(comstr);
	}

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	// Set up some random, and non-repeating values
	// {{{
	testbuf  = new uint32_t[NLEN];
	checkbuf = new uint32_t[NLEN*2];
	ovbuf    = new uint32_t[NLEN*2];
	for(unsigned k=0; k<NLEN; k++) {
		bool	dup;

		do {
			dup = false;

			testbuf[k] = rand();
			if ((k & 0x07)==0)
				testbuf[k] &= ~0x0ff;
			else if (0 == (k & 0x3f))
				testbuf[k] &= ~0x07fff;
			for(unsigned j=0; j<k; j++) {
				if (testbuf[k] == testbuf[j]) {
					dup = true;
					break;
				}
			}
		} while(dup);
	}
	// }}}

	for(unsigned offset=511; (offset<NLEN) && passed; offset++) {
		// {{{
		printf("Read check, testing offset  %d\n", offset);

		// Write this data to the device
		printf("\tWRITE"); fflush(stdout);
		m_fpga->writei(R_BKRAM, NLEN, testbuf);
		// Write it again, this time with an offset
		printf(", WRITE"); fflush(stdout);
		m_fpga->writei(R_BKRAM + 4*offset, NLEN, testbuf);
		// Now, read both back
		printf(", READ"); fflush(stdout);
		m_fpga->readi(R_BKRAM, NLEN + offset, checkbuf);
		// ... and compare the result
		printf(", CHECK\n"); fflush(stdout);
		for(unsigned k=0; k<offset; k++) {
			if (checkbuf[k] != testbuf[k]) {
				printf("RD-ERR: CHECK[%d]=%08x != 0x%08x (expected)\n", k, checkbuf[k], testbuf[k]);
				passed = false;
			}
		} for(unsigned k=0; k<NLEN; k++) {
			if (checkbuf[offset+k] != testbuf[k]) {
				printf("RD-ERR: CHECK[%d+%d]=%08x != 0x%08x (expected)\n", offset, k, checkbuf[offset+k], testbuf[k]);
				passed = false;
			}
		}
	}
	// }}}

	for(unsigned offset=0; (offset<NLEN) && passed; offset++) {
		// {{{
		printf("Write check, testing offset  %d\n", offset);
		for(unsigned k=0; k<offset; k++)
			ovbuf[k] = testbuf[k];
		for(unsigned k=0; k<NLEN; k++)
			ovbuf[offset+k] = testbuf[k];

		printf("\tWRITE"); fflush(stdout);
		m_fpga->writei(R_BKRAM, NLEN + offset, ovbuf);
		// Now, read both back
		printf(", READ"); fflush(stdout);
		m_fpga->readi(R_BKRAM, NLEN + offset, checkbuf);
		// ... and compare the result
		printf(", CHECK\n"); fflush(stdout);
		for(unsigned k=0; k<NLEN+offset; k++) {
			if (checkbuf[k] != ovbuf[k]) {
				printf("WR-ERR: CHECK[%d+%d]=%08x != 0x%08x (expected)\n", offset, k, checkbuf[k], ovbuf[k]);
				passed = false;
			}
		}
	}
	// }}}

	if (passed) printf("SUCCESS!\n");

	if (m_fpga->poll())
		printf("FPGA was interrupted\n");
	delete	m_fpga;
}

