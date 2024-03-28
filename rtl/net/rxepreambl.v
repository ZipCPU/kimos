////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/net/rxepreambl.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	To detect, and then remove, any ethernet hardware preamble.
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
`default_nettype	none
// }}}
module	rxepreambl (
		// {{{
		input	wire		i_clk, i_reset, i_ce, i_en,
		input	wire		i_v,
		input	wire	[7:0]	i_d,
		output	reg		o_v,
		output	reg	[7:0]	o_d
		// }}}
	);

	// Local declarations
	// {{{
	reg	r_inpkt;
	reg	[3:0]	nsyncs;
	// }}}

	// nsyncs
	// {{{
	initial	nsyncs  = 0;
	always @(posedge i_clk)
	if (i_reset)
		nsyncs <= 0;
	else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
			nsyncs <= 0;
		else if ((i_d == 8'h55)&&(i_v))
		begin
			if (! (&nsyncs))
				nsyncs <= nsyncs + 1'b1;
		end else
			nsyncs <= 0;
	end
	// }}}

	// o_v, o_d
	// {{{
	initial	o_v = 1'b0;
	initial	o_d = 8'h0;
	initial	r_inpkt = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_inpkt <= 1'b0;
		o_v     <= 1'b0;
		o_d     <= 8'h0;
	end else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
		begin
			// Soft reset
			//
			// Set us up for the next packet
			r_inpkt <= 1'b0;
			o_v <= 1'b0;
			o_d <= 8'h0;
		end else if (!r_inpkt)
		begin
			r_inpkt <= (nsyncs > 4'h6)&&(i_v)&&(i_d == 8'hd5);
			o_v <= 1'b0;
			o_d <= 8'h0;
		end else begin
			o_v <= (i_v);
			o_d <= (i_v) ? i_d : 8'h0;
		end

		if (!i_en)
		begin
			o_v <= i_v;
			o_d <= (i_v) ? i_d : 8'h0;
		end
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
	reg	[6:0]	f_match;
	reg	[7:0]	f_d;
	reg		f_v;
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if ((i_v)||(o_v))
		assume($stable(i_en));

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assume(!i_v);
	end else if (!$past(i_ce))
		assume($stable(i_v));

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if ($past(i_v || o_v))
		assume($stable(i_en));

	always @(posedge i_clk)
	if (!$past(i_ce))
	begin
		assume($stable(i_v));
		assume($stable(i_d));
	end

	always @(posedge i_clk)
	if ((o_v)&&(!$past(i_v)))
		assume(!i_v);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Safety properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= i_v;

	initial	f_match = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_match <= 0;
	else if (i_ce)
	begin
		f_d <= i_d;
		if ((i_v)&&(i_d == 8'h55))
			f_match <= { f_match[5:0], (i_d == 8'h55) };
		else
			f_match <= 0;
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_v))
		assert(o_d == f_d[7:0]);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!r_inpkt);
	end else if (!$past(i_ce))
	begin
		assert($stable(r_inpkt));
	end else if ($past(&f_match) && f_v && $past(nsyncs >= 6) && ($past(i_d) == 8'hd5))
		assert(r_inpkt);

	always @(posedge i_clk)
	if (o_v && i_en)
		assert(r_inpkt);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_en))&&(!$past(i_reset))
			&&($past(nsyncs>4'h6))&&(f_v)
			&&($past(i_d == 8'hd5))
			&&($past(i_ce)))
	begin
		assert(r_inpkt);
	end else if ((f_past_valid)&&($past(i_en))&&(!$past(r_inpkt)))
		assert(!o_v);

	// always @(posedge i_clk)
	// if ((f_past_valid)&&(!$past(i_reset))&&($past(r_inpkt))&&(f_v))
	//	assert(o_v);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_v);
	end else if ((f_v)&&($past(o_v)))
	begin
		assert(o_v);
	end else if ((f_v)&&($past(i_ce && !i_en)))
		assert(o_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_en)))
	begin
		if (o_v)
		begin
			assert(o_d == f_d);
		end else
			assert(o_d == 8'h0);
	end

	always @(posedge i_clk)
	case(nsyncs)
	4'h0: assert(f_match == 0);
	4'h1: assert(f_match == 6'h01);
	4'h2: assert(f_match == 6'h03);
	4'h3: assert(f_match == 6'h07);
	4'h4: assert(f_match == 6'h0f);
	4'h5: assert(f_match == 6'h1f);
	default: begin end
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
		cover(o_v);

	always @(posedge i_clk)
		cover(o_v && i_en);
	// }}}
`endif
// }}}
endmodule

