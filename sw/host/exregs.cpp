////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/exregs.cpp
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	To give a user access, via a command line program, to read
//		and write wishbone registers one at a time.  Thus this program
//	accesses the readio() and writeio() methods from devbus, but nothing
//	more.
//
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
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

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

unsigned getmap_address(const char *map_fname, const char *name) {
	FILE	*fmp = fopen(map_fname, "r");
	char	line[512];

	if (NULL == fmp) {
		fprintf(stderr, "ERR: Could not open MAP file, %s\n", map_fname);
		exit(EXIT_FAILURE);
	}

	while(fgets(line, sizeof(line), fmp)) {
		char	*astr, *nstr, *xstr;

		astr = strtok(line, " \t\n");
		if (!astr)
			continue;
		nstr = strtok(NULL, " \t\n");
		if (!nstr)
			continue;
		xstr = strtok(NULL, " \t\n");
		if (xstr)
			continue;
		if (!isvalue(astr))
			continue;
		if (0 == strcasecmp(nstr, name))
			return strtoul(astr, NULL, 0);
	}
	
	fclose(fmp);
	return 0;
}

char	*getmap_name(const char *map_fname, const unsigned val) {
	if (!map_fname)
		return NULL;
	FILE	*fmp = fopen(map_fname, "r");
	char	line[512];
	if (NULL == fmp) {
		fprintf(stderr, "ERR: Could not open MAP file, %s\n", map_fname);
		exit(EXIT_FAILURE);
	}

	while(fgets(line, sizeof(line), fmp)) {
		char	*astr, *nstr, *xstr;

		astr = strtok(line, " \t\n");
		if (!astr)
			continue;
		nstr = strtok(NULL, " \t\n");
		if (!nstr)
			continue;
		xstr = strtok(NULL, " \t\n");
		if (xstr)
			continue;
		if (!isvalue(astr))
			continue;
		if (strtoul(astr, NULL, 0) == val)
			return strdup(nstr);
	}
	
	fclose(fmp);
	return NULL;
}

void	usage(void) {
	printf("USAGE: exregs [-d] address [value]\n"
"\n"
"\tWBREGS stands for Wishbone registers.  It is designed to allow a\n"
"\tuser to peek and poke at registers within a given FPGA design, so\n"
"\tlong as those registers have addresses on the wishbone bus.  The\n"
"\taddress may reference peripherals or memory, depending upon how the\n"
"\tbus is configured.\n"
"\n"
"\t-d\tIf given, specifies the value returned should be in decimal,\n"
"\t\trather than hexadecimal.\n"
"\n"
"\t-m [mapfile]\tA \"map file\" may be created by the ZipCPU linker.\n"
"\t\tSuch a file can then be used to access named global values\n"
"\t\twithin the register space.  To use the capability, the name of\n"
"\t\tthe map file must be provided here on the command line.\n"
"\t-n [host]\tAttempt to connect, via TCP/IP, to host named [host].\n"
"\t\tThe default host is \'%s\'\n"
"\n"
"\t-p [port]\tAttempt to connect, via TCP/IP, to port number [port].\n"
"\t\tThe default port is \'%d\'\n"
"\n"
"\tAddress is either a 32-bit value with the syntax of strtoul, or a\n"
"\tregister name.  Register names can be found in regdefs.cpp\n"
"\n"
"\tIf a value is given, that value will be written to the indicated\n"
"\taddress, otherwise the result from reading the address will be \n"
"\twritten to the screen.\n", FPGAHOST, FPGAPORT);
}

int main(int argc, char **argv) {
	bool	use_decimal = false;
	const char *host = FPGAHOST;
	int	port=FPGAPORT;
	char	*map_file = NULL;
	int	opt;

	// Process all arguments, save the address and optional value
	// {{{
	while(-1 != (opt=getopt(argc, argv, "dn:p:m:"))) {
		switch(opt) {
		case 'd': use_decimal = true; break;
		case 'h': usage(); exit(EXIT_SUCCESS); break;
		case 'n': host = strdup(optarg); break;
		case 'p': port = strtoul(optarg, NULL, 0); break;
		case 'm': map_file = strdup(optarg); break;
		default: usage();
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

	if ((argc-optind < 1)||(argc-optind > 2)) {
		// {{{
		usage();
		exit(EXIT_FAILURE);
	}
	// }}}

	if ((map_file)&&(0 != access(map_file, R_OK))) {
		// {{{
		fprintf(stderr, "ERR: Cannot open/read map file, %s\n", map_file);
		exit(EXIT_FAILURE);
	}
	// }}}

	const char *nm = NULL, *named_address = argv[optind];
	unsigned address, value;

	if (isvalue(named_address)) {
		address = strtoul(named_address, NULL, 0);
		if (map_file)
			nm = getmap_name(map_file, address);
		if (nm == NULL)
			nm = addrname(address);
	} else if (map_file) {
		address = getmap_address(map_file, named_address);
		nm = getmap_name(map_file, address);
		if (!nm) {
			address = addrdecode(named_address);
			nm = addrname(address);
		}
	} else {
		address = addrdecode(named_address);
		nm = addrname(address);
	}

	if (NULL == nm)
		nm = "";

	if (argc -optind < 2) { // Read from the device
		// {{{
		FPGA::BUSW	v;
		try {
			unsigned char a, b, c, d;
			v = m_fpga->readio(address);
			a = (v>>24)&0x0ff;
			b = (v>>16)&0x0ff;
			c = (v>> 8)&0x0ff;
			d = (v    )&0x0ff;
			if (use_decimal)
				printf("%d\n", v);
			else
			printf("%08x (%8s) : [%c%c%c%c] %08x\n", address, nm, 
				isgraph(a)?a:'.', isgraph(b)?b:'.',
				isgraph(c)?c:'.', isgraph(d)?d:'.', v);
		} catch(BUSERR b) {
			printf("%08x (%8s) : BUS-ERROR\n", address, nm);
		} catch(const char *er) {
			printf("Caught bug: %s\n", er);
			exit(EXIT_FAILURE);
		}
		// }}}
	} else { // Write to the device
		// {{{
		try {
			value = strtoul(argv[optind+1], NULL, 0);
			m_fpga->writeio(address, value);
			printf("%08x (%8s)-> %08x\n", address, nm, value);
		} catch(BUSERR b) {
			printf("%08x (%8s) : BUS-ERR)R\n", address, nm);
			exit(EXIT_FAILURE);
		} catch(const char *er) {
			printf("Caught bug on write: %s\n", er);
			exit(EXIT_FAILURE);
		}
		// }}}
	}

	if (m_fpga->poll())
		printf("FPGA was interrupted\n");
	delete	m_fpga;
}

