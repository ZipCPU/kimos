////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/rxemin.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	To force the minimum received packet size of an ethernet frame
//		to be a minimum of 64 bytes.  Packets less than 64-bytes
//	(including CRC) will be dropped here.  This module handles that logic.
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
`default_nettype	none
// }}}
module rxemin #(
		// {{{
		parameter	MINBYTES=60,
		localparam	LGNCOUNT= $clog2(MINBYTES+2)
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset, i_ce, i_en,
		input	wire		i_v,	// Valid
		output	reg		o_err
		// }}}
	);

	// Local declarations
	// {{{
	reg			last_v;
	reg	[LGNCOUNT:0]	r_ncnt;
	// }}}

	// last_v
	// {{{
	initial	last_v = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_v <= 1'b0;
	else if (i_ce)
		last_v <= i_v;
	// }}}

	// o_err, r_ncnt
	// {{{
	initial	o_err  = 0;
	initial	r_ncnt = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// Here's our reset.  If the input isn't valid (i.e., no
		// packet present), or if we are cancelling the packet,
		// then we come in here and reset our interface.
		r_ncnt <= 0;
		o_err <= 0;
	end else if (i_ce)
	begin
		if ((!last_v)&&(!i_v))
		begin
			// Also a reset of sorts
			r_ncnt <= 0;
			o_err <= 0;
		end else if (i_v)
		begin
			if (!r_ncnt[LGNCOUNT])
				r_ncnt <= r_ncnt + 1'b1;
			o_err <= 0;
		end else //  if ((!i_reset)&&(!i_v)&&(last_v))
			o_err <= (i_en)&&(!r_ncnt[LGNCOUNT])
						&&(r_ncnt < MINBYTES);
	end
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	[1:0]	f_v;
	reg		f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Input assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_err && i_ce)))
		assume(!i_v);


	always @(posedge i_clk)
	if ((f_past_valid)&&(i_v || $past(i_v)))
		assume(i_en == $past(i_en));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Safety Assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[0], i_v };

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_err);
	end else if ($past(o_err && i_ce))
		assert(!o_err);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_ce)))
		assert($past(i_v)==last_v);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset))||(f_v == 0))
	begin
		assert(r_ncnt == 0);
		assert(o_err  == 0);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(r_ncnt) > MINBYTES)&&($past(i_v)))
		assert(r_ncnt > MINBYTES);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover statements
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
		cover(r_ncnt > MINBYTES);
	always @(posedge i_clk)
		cover(o_err);
	always @(posedge i_clk)
		cover(r_ncnt > MINBYTES && $fell(i_v));
	// }}}
`endif
// }}}
endmodule
