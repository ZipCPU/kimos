////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/byteswap.h
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
#ifndef	BYTESWAP_H
#define	BYTESWAP_H

#include <stdint.h>

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
extern	uint32_t byteswap(uint32_t v);
extern	void	byteswapbuf(int ln, uint32_t *buf);
#else
#define	byteswap(A)		 (A)
#define	byteswapbuf(A, B)
#endif

extern	uint32_t buildword(const unsigned char *p);
extern	uint32_t buildswap(const unsigned char *p);

#endif
