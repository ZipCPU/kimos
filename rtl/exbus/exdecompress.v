////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exdecompress.v
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
// Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	exdecompress #(
		// {{{
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk,
					i_reset,
					i_stb,
		output	wire		o_busy,
		input	wire	[34:0]	i_word,
		output	reg		o_stb,
		input	wire		i_busy,
		output	reg	[34:0]	o_word,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	reg	[34:0]	addr_word;
	reg	[34:0]	write_word;
	reg	[9:0]	write_lookup_addr, write_addr;
	reg		write_table_lookup;
	reg	[11:0]	read_count;
	reg		partial_type;
	reg	[31:0]	write_table	[0:(1<<10)-1];

	reg	[1:0]	word_type;
	reg		r_stb, q_stb;
	reg	[4:0]	r_special;
	reg	[34:0]	partial;
	reg	[31:0]	write_table_value;
	reg		write_to_table;

	wire	r_busy, q_busy;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock #1:
	//	From:	i_stb, i_word
	//	Create:	r_stb, addr_word, write_word, write_lookup_addr
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Decode the address
	//	Address output is 2'b00, 1'b0, address (if fixed)
	//			2'b00, 1'b1, address offset

	// addr_word
	// {{{
	always @(posedge i_clk)
	if (!OPT_LOWPOWER || (i_stb && !o_busy && i_word[34:33] == 2'b00))
	casez(i_word[32:29])
	4'b0???:addr_word <= { 3'b000, i_word[31:2], 1'b0, i_word[0] };
	4'b10??:addr_word <= { 3'b001, {(29){i_word[30]}}, i_word[29], 1'b0, i_word[28] };
	4'b1100:addr_word <= { 3'b000, {(24){i_word[28]}}, i_word[27:22], 1'b0, i_word[21] };
	4'b1101:addr_word <= { 3'b001, {(24){i_word[28]}}, i_word[27:22], 1'b0, i_word[21] };
	4'b1110:addr_word <= { 3'b000, {(17){i_word[28]}}, i_word[27:15], 1'b0, i_word[14] };
	4'b1111:addr_word <= { 3'b001, {(17){i_word[28]}}, i_word[27:15], 1'b0, i_word[14] };
	endcase
	// }}}

	// write_word: Decode the write word
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	casez(i_word[34:30])
	5'b??0??:write_word <= { 3'b010, i_word[31:0] };
	5'b??1?0:write_word <= { 3'b010, {(24){i_word[29]}}, i_word[28:21] };
	5'b??1?1:write_word <= { 3'b010, {(17){i_word[29]}}, i_word[28:14] };
	endcase
	// }}}

	// write_lookup_addr
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	begin
		if (OPT_LOWPOWER && i_word[34:33] != 2'b01)
			write_lookup_addr <= 0;
		else case(i_word[30])
		1'b0:write_lookup_addr<= { 8'hff, ~i_word[29:28] } + write_addr;
		1'b1:write_lookup_addr<= { 1'b1,  ~i_word[29:21] } + write_addr;
		endcase
	end
	// }}}

	// write_table_lookup
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		write_table_lookup <= 1'b0;
	else if (i_stb && !o_busy)
	begin
		if (OPT_LOWPOWER)
			write_table_lookup <= (i_word[34:31] == 4'b0110);
		else
			write_table_lookup <= (i_word[32:31] == 2'b10);
	end else if (!r_busy)
		write_table_lookup <= 1'b0;
	// }}}

	// read_count
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		read_count <= 0;
	else if (i_stb && !o_busy)
	case(i_word[32])
	1'b0: read_count <= 12'd1  + { 8'h0, i_word[31:28] }; // 1-16
	1'b1: read_count <= 12'd17 + { 1'b0, i_word[31:21] };	// 17-2064
	endcase
	// }}}

	// word_type
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		word_type <= 2'b00;
	else if (i_stb && !o_busy)
		word_type <= i_word[34:33];
	// }}}

	// r_stb, r_special, write_to_table
	// {{{
	initial	r_stb = 1'b0;
	initial	write_to_table = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_stb <= 1'b0;
		write_to_table <= 1'b0;
	end else if (i_stb && !o_busy)
	begin
		r_stb <= 1'b1;
		write_to_table <= i_word[34:33] == 2'b01
			&& (!i_word[32] || i_word[32:30] == 3'b111);
	end else if (!r_busy)
		{ write_to_table, r_stb } <= 2'b0;

	always @(posedge i_clk)
	if (i_stb && !o_busy)
		r_special <= i_word[32:28];
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock #2:
	//	Create: q_stb, partial, partial_type, write_table,
	//		write_table_value
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// q_stb
	// {{{
	initial	q_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		q_stb <= 1'b0;
	else if (r_stb && !r_busy)
		q_stb <= 1'b1;
	else if (!q_busy)
		q_stb <= 1'b0;
	// }}}

	// partial
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		partial <= 35'h0;
	else if (r_stb && !r_busy)
	case(word_type)
	2'b00: partial <=  addr_word;
	2'b01: partial <= write_word;
	2'b10: partial <= { 2'b10, {(21){1'b0}}, read_count };
	2'b11: partial <= { 2'b11, r_special, 28'h0 };
	endcase
	// }}}

	// partial_type
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		partial_type <= 1'b0;
	else if (r_stb && !r_busy)
		partial_type <= write_table_lookup && word_type == 2'b01;
	// }}}

	// Write to our compression table
	// {{{
	always @(posedge i_clk)
	if (write_to_table && !r_busy)
		write_table[write_addr] <= write_word[31:0];
	// }}}

	// write_addr
	// {{{
	initial	write_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		write_addr <= 0;
	else if (write_to_table && !r_busy)
		write_addr <= write_addr + 1;
	// }}}

	// write_table_value
	// {{{
	always @(posedge i_clk)
	if (write_table_lookup && !r_busy)
		write_table_value <= write_table[write_lookup_addr];
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock #3:
	//	Create: o_stb, o_word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (q_stb && !q_busy)
		o_stb <= 1'b1;
	else if (!i_busy)
		o_stb <= 1'b0;
	// }}}

	// o_word
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		o_word <= 0;
	else if (q_stb && !q_busy && partial_type)
		o_word <= { 3'b010, write_table_value };
	else
		o_word <= partial;
	// }}}

	assign	q_busy = o_stb && i_busy;
	assign	r_busy = q_stb && q_busy;
	assign	o_busy = r_stb && r_busy;
	assign	o_active = r_stb || q_stb;
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
`endif
// }}}
endmodule

