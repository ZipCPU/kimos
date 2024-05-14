////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./iscachable.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga -I / -d -o . allclocks.txt clkcheck.txt global.txt crossbus.txt icape.txt version.txt pic.txt pwrcount.txt rtccount.txt spio.txt exconsole.txt wbuuart.txt wbuarbiter.txt bkram.txt flash.txt flashcfg.txt sdram.txt mem_sdram_only.txt mem_flash_sdram.txt zipmaster.txt mdio.txt meganet.txt protocols.txt eth0bus.txt sdio.txt flashscope.txt sdioscope.txt mem_flash_bkram.txt mem_bkram_only.txt xdc.txt i2ccpu.txt
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
`default_nettype none
//
module iscachable(
		// {{{
		input	wire	[31-1:0]	i_addr,
		output	reg			o_cachable
		// }}}
	);

	always @(*)
	begin
		o_cachable = 1'b0;
		// Bus master: wbwide
		// Bus master: wbflash
		// flash
		if ((i_addr[30:0] & 31'h7c000000) == 31'h04000000)
			o_cachable = 1'b1;
		// Bus master: wb32
		// Bus master: wb32_sio
		// bkram
		if ((i_addr[30:0] & 31'h7e000000) == 31'h0a000000)
			o_cachable = 1'b1;
		// sdram
		if ((i_addr[30:0] & 31'h40000000) == 31'h40000000)
			o_cachable = 1'b1;
	end

endmodule
