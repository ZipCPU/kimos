////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/fatfs/sdiodrv.h
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
#ifndef	SDIODRV_H
#define	SDIODRV_H

typedef	struct SDIO_S {
	volatile uint32_t	sd_cmd, sd_data, sd_fifa, sd_fifb, sd_phy;
} SDIO;

struct	SDIODRV_S;

extern	struct	SDIODRV_S *sdio_init(SDIO *dev);
extern	int	sdio_write(struct SDIODRV_S *dev, const unsigned sector, const unsigned count, const char *buf);
extern	int	sdio_read(struct SDIODRV_S *dev, const unsigned sector, const unsigned count, char *buf);
extern	int	sdio_ioctl(struct SDIODRV_S *dev, char cmd, char *buf);
#endif
