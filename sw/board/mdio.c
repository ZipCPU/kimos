////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/mdio.c
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	Decode MDIO registers, dump them and any abnormal conditions
//		to standard-out.
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
#include "board.h"

int main(int argc, char **argv) {
#ifdef	_BOARD_HAS_NETMDIO
	unsigned	nreg, iface;

	for(iface=0; iface < 32; iface++) {
		nreg = _mdio->e_v[iface][MDIO_CONTROL] & 0x0ffff;
		if (0x0ffff == (nreg & 0x0ffff)) {
			printf("%-12s[0x%2x]  : 0x%04x --> NO PHY\n", "MDIO Status", iface, nreg);
			// if (0x3 != (iface & 0x1b))
			continue;
		}

		printf("------------------------------------------------\n");
		printf("--  PHY ADDR 0x%02x, starting at 0x%08x\n", iface,
			(unsigned)&_mdio->e_v[iface][MDIO_CONTROL]);
		printf("------------------------------------------------\n");
		nreg = _mdio->e_v[iface][MDIO_CONTROL] & 0x0ffff;
		printf("%-12s[0x%2x]  : 0x%04x\n", "MDIO Control", iface, nreg);
		if (nreg & 0x8000)
			printf("\tSoftware PHY reset\n");
		if (nreg & 0x4000)
			printf("\tLoopback\n");
		if (0 == (nreg & 0x1000)) {
			printf("\tAutonegotiation disabled\n");
			if (0 == (nreg & 0x2040))
				printf("\t10Mb/s\n");
			else if (0x0040 == (nreg & 0x2040))
				printf("\t100Mb/s\n");
			else if (0x2000 == (nreg & 0x2040))
				printf("\t1Gb/s\n");
			else if (0x2040 == (nreg & 0x2040))
				printf("\t(Reserved?\?)\n");
		}
		if (0 != (nreg & 0x0800))
			printf("\tPowered down\n");
		if (0 != (nreg & 0x0400))
			printf("\tIsolated PHY\n");
		if (0 != (nreg & 0x0200))
			printf("\tAutonegiation restart (?)\n");
		if (0 == (nreg & 0x0100))
			printf("\tHalf duplex mode\n");

		nreg = _mdio->e_v[iface][MDIO_STATUS] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "MDIO Status", nreg);
#ifdef	_BOARD_HAS_MDIOSCOPE
		// Reset the scope once, before the next read, but do it early
		// enough that the scope can complete its reset.
		if (iface == 3)
			_mdioscope->s_ctrl = 0x0fe;
#endif
		if (nreg & 0x8000)
			printf("\tT4 capable\n");
		if (0 == (nreg & 0x4000))
			printf("\tNo capability for 100Mbps full-duplex\n");
		if (0 == (nreg & 0x2000))
			printf("\tNo capability for 100Mbps half-duplex\n");
		if (0 == (nreg & 0x1000))
			printf("\tNo capability for  10Mbps full-duplex\n");
		if (0 == (nreg & 0x0800))
			printf("\tNo capability for  10Mbps half-duplex\n");
		if (nreg & 0x0040)
			printf("\tPre-amble suppression\n");
		if (0 == (nreg & 0x0020))
			printf("\tAuto-negotiation not complete\n");
		if (0 != (nreg & 0x0010))
			printf("\tREMOTE FAULT!\n");
		if (0 == (nreg & 0x0008))
			printf("\tCannot perform auto-negotiation\n");
		if (0 == (nreg & 0x0004))
			printf("\tLink is down\n");

		nreg = _mdio->e_v[iface][MDIO_PHYIDR1] & 0x0ffff;
		printf("%-20s: 0x%04x.  Should be either 0x0022, or 0x0214\n", "PHY ID #1(0022h)", nreg); 
		nreg = _mdio->e_v[iface][MDIO_PHYIDR2] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "PHY ID #2", nreg);

		nreg = _mdio->e_v[iface][MDIO_ANAR] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "Auto Advertisement", nreg);
		if (0 == (nreg & 0x2000))
			printf("\tNo remote fault support\n");
		if (0 == (nreg & 0x0400))
			printf("\tNo T4 capability\n");
		if (0 == (nreg & 0x0100))
			printf("\tNo 100MBps full-duplex capability\n");
		if (0 == (nreg & 0x0080))
			printf("\tNo 100MBps half-duplex capability\n");
		if (0 == (nreg & 0x0040))
			printf("\tNo  10MBps full-duplex capability\n");
		if (0 == (nreg & 0x0020))
			printf("\tNo  10MBps half-duplex capability\n");

		nreg = _mdio->e_v[iface][MDIO_ANER] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "Link partner ability", nreg);
		if (nreg & 0x2000)
			printf("\tRemote fault detected\n");
		if (0 == (nreg & 0x0400))
			printf("\tNo T4 capability\n");
		if (0 == (nreg & 0x0100))
			printf("\tNo 100MBps full-duplex capability\n");
		if (0 == (nreg & 0x0080))
			printf("\tNo 100MBps half-duplex capability\n");
		if (0 == (nreg & 0x0040))
			printf("\tNo  10MBps full-duplex capability\n");
		if (0 == (nreg & 0x0020))
			printf("\tNo  10MBps half-duplex capability\n");

		nreg = _mdio->e_v[iface][MDIO_ANNPTR] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "Auto-neg expansion", nreg);
		nreg = _mdio->e_v[iface][MDIO_ANNPRR] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "Auto-neg next-page", nreg);
		nreg = _mdio->e_v[iface][MDIO_GBCR] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "GBase-T Control", nreg);
		if (0 != (nreg & 0xe000))
			printf("\tAbnormal test mode setting: %s\n", (nreg>>13)&7);
		if (0 != (nreg & 0x1000)) {
			printf("\tManual master-slave configuration enabled\n");
			if (0 != (nreg & 0x0800))
				printf("\tPHY confgiured as master\n");
			if (0 == (nreg & 0x0800))
				printf("\tPHY confgiured as slave\n");
		}
		if (0 == (nreg & 0x0200))
			printf("\tAdvertising as incapable of Gbase-T full-duplex\n");
		if (0 == (nreg & 0x0100))
			printf("\tAdvertising as incapable of Gbase-T half-duplex\n");

		nreg = _mdio->e_v[iface][MDIO_GBSR] & 0x0ffff;
		printf("%-20s: 0x%04x\n", "GBase-T Status", nreg);
		if (0 != (nreg & 0x8000))
			printf("\tConfiguration fault detected\n");
		if (0 == (nreg & 0x2000))
			printf("\tLocal receiver not okay\n");
		if (0 == (nreg & 0x1000))
			printf("\tRemote receiver not okay\n");
		if (0 == (nreg & 0x0800))
			printf("\tLink partner has NO Gbase-T full-duplex capability\n");
		if (0 == (nreg & 0x0400))
			printf("\tLink partner has NO Gbase-T half-duplex capability\n");

		// nreg = _mdio->e_v[iface][MDIO_MACR] & 0x0ffff;
		// nreg = _mdio->e_v[iface][MDIO_MAADR] & 0x0ffff;
		// nreg = _mdio->e_v[iface][MDIO_GBESR] & 0x0ffff;
		// nreg = _mdio->e_v[iface][MDIO_LOOPBACK];
	}
#else
	printf("ERR: No MDIO peripheral\n");
#endif
}
