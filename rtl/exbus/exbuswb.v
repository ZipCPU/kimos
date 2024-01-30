////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exbuswb.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	This is the top level component for the exbus when attached
//		to a Wishbone bus.
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
module	exbuswb #(
		// {{{
		parameter	ADDRESS_WIDTH=30,	// Width in log2(words)
		localparam	AW=ADDRESS_WIDTH, // Shorthand for address width
			DW=32			// Shorthand for bus data width
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		output	wire			o_reset,
		// The input channel from the serial port
		// {{{
		input	wire			i_rx_stb,
		input	wire	[7:0]		i_rx_byte,
		// }}}
		// The return serial port channel
		// {{{
		output	reg			o_tx_stb,
		output	reg	[7:0]		o_tx_byte,
		input	wire			i_tx_busy,
		// }}}
		// GPIO interface
		// {{{
		input	wire	[1:0]		i_gpio,
		output	wire	[1:0]		o_gpio,
		// }}}
		// Console interface
		// {{{
		input	wire			i_console_stb,
		input	wire	[6:0]		i_console_byte,
		output	reg			o_console_busy,
		//
		output	reg			o_console_stb,
		output	reg	[6:0]		o_console_byte,
		// }}}
		// Wishbone
		// {{{
		output	wire			o_wb_cyc,
		output	reg			o_wb_stb,
		output	reg			o_wb_we,
		output	reg	[(AW-1):0]	o_wb_addr,
		output	reg	[DW-1:0]	o_wb_data,
		output	wire	[DW/8-1:0]	o_wb_sel,
		// Wishbone inputs
		input	wire			i_wb_stall, i_wb_ack, i_wb_err,
		input	wire	[DW-1:0]	i_wb_data,
		// }}}
		input	wire			i_interrupt
		// }}}
	);

	// Local declarations
	// {{{
	localparam	CW=35;	// Command word width
	wire			iword_stb, cmd_reset;
	wire	[CW-1:0]	iword_data;
	wire			in_stb;
	wire	[CW-1:0]	in_data;
	wire			bus_rd_busy;
	wire			ififo_valid, ififo_err;
	wire	[CW-1:0]	ififo_data;
	wire			ofifo_valid, ofifo_err;
	wire	[CW-1:0]	ofifo_data;
	wire			compress_valid, compress_busy;
	wire	[CW-1:0]	compress_data;
	wire			idle_valid, idle_busy;
	wire	[CW-1:0]	idle_data;
	wire			deword_valid, deword_busy;
	wire	[6:0]		deword_byte;
	wire			bus_stb;
	wire	[CW-1:0]	bus_word;
	wire			out_busy;
	// }}}

	// o_console_stb, o_console_byte
	// {{{
	initial	o_console_stb = 1'b0;
	always @(posedge i_clk)
	begin
		o_console_stb  <= (i_rx_stb && !i_rx_byte[7]);
		o_console_byte <= i_rx_byte[6:0];
	end
	// }}}

	// exmkword: iword_stb, iword_data, cmd_reset
	// {{{
	exmkword
	mkword(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(i_rx_stb && i_rx_byte[7]),
			.i_data(i_rx_byte[6:0]),
		.o_stb(iword_stb), .o_data(iword_data),
		.o_reset_bridge(cmd_reset),
		.o_reset_design(o_reset)
		// }}}
	);
	// }}}

	// exdecompress: iword_* -> in_stb, in_data
	// {{{
	exdecompress
	decompress(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_stb(iword_stb), .i_word(iword_data),
		.o_stb(in_stb), .o_word(in_data)
		// }}}
	);
	// }}}

	// wbufifo: Incoming FIFO, in_* -> ififo_data, ififo_valid, ififo_err
	// {{{
	wbufifo #(
		// {{{
		.BW(CW), .LGFLEN(5)
		// }}}
	) ififo(
		// {{{
		.i_clk(i_clk), .i_reset(cmd_reset),
		.i_wr(in_stb), .i_data(in_data),
		.i_rd(!bus_rd_busy && ififo_valid), .o_data(ififo_data),
			.o_empty_n(ififo_valid), .o_err(ififo_err)
		// }}}
	);
	// }}}

	// o_gpio
	// {{{
	always @(posedge i_clk)
	if (i_reset || cmd_reset)
		o_gpio <= 2'b00;
	else if (ififo_valid && !bus_rd_busy && ififo_data[34:33] == 2'b11)
		o_gpio <= ififo_data[32:31];
	// }}}

	// exwb: Drive the bus: ififo_* -> Wishbone -> bus_stb, bus_word
	// {{{
	exwb #(.ADDRESS_WIDTH(AW))
	genbus(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_cmd_stb(ififo_valid),
			.i_cmd_word(ififo_data),
			.o_cmd_busy(bus_rd_busy),
		.o_cmd_stb(bus_stb), .o_cmd_word(bus_word),
		.o_wb_cyc(o_wb_cyc), .o_wb_stb(o_wb_stb), .o_wb_we(o_wb_we),
			.o_wb_addr(o_wb_addr), .o_wb_data(o_wb_data),
			.o_wb_sel(o_wb_sel),
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
			.i_wb_data(i_wb_data), .i_wb_err(i_wb_err)
		// }}}
	);
	// }}}

	// wbufifo: Outgoing FIFO, bus_* -> ofifo_data, ofifo_valid, ofifo_err
	// {{{
	wbufifo #(
		// {{{
		.BW(35), .LGFLEN(5)
		// }}}
	) ofifo(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_wr(bus_stb), .i_data(bus_word),
		.i_rd(!compress_busy && ofifo_valid), .o_data(ofifo_data),
			.o_empty_n(ofifo_valid), .o_err(ofifo_err)
		// }}}
	);
	// }}}

	// excompress: idle_*, compress_valid, compress_data
	// {{{
	excompress
	compress(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_stb(ofifo_valid), .i_word(ofifo_data),
			.o_busy(compress_busy),
		.o_stb(compress_valid), .o_word(compress_data),
			.i_busy(idle_busy)
		// }}}
	);
	// }}}

	// exidle: ofifo* -> idle_valid, idle_data
	// {{{
	exidle
	idle(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_stb(compress_valid), .i_word(compress_data),
			.o_busy(idle_busy),
		.i_aux(i_gpio), .i_cts(1'b1), .i_int(i_interrupt),
			.i_fifo_err(ofifo_err || ififo_err),
		.o_stb(idle_valid), .o_word(idle_data), .i_busy(deword_busy)
		// }}}
	);
	// }}}

	// exdeword: -> deword_valid, deword_byte
	// {{{
	exdeword
	deword(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),//.i_gpio(i_gpio),
		.i_stb(idle_valid), .i_word(idle_data),
			.o_busy(deword_busy),
		.o_stb(deword_valid), .o_byte(deword_byte), .i_busy(out_busy)
		// }}}
	);
	// }}}

	// out_busy
	// {{{
	assign	out_busy = (o_tx_stb && i_tx_busy) || i_console_stb;
	// }}}

	// o_tx_stb
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		o_tx_stb <= 1'b0;
	else if (!o_tx_stb || !i_tx_busy)
		o_tx_stb <= i_console_stb || deword_valid;
	// }}}

	// o_tx_byte
	// {{{
	always @(posedge i_clk)
	if (!o_tx_stb || !i_tx_busy)
	begin
		if (i_console_stb)
			o_tx_byte <= { 1'b0, i_console_byte };
		else
			o_tx_byte <= { 1'b1, deword_byte };
	end
	// }}}

	assign	o_console_busy = o_tx_stb && i_tx_busy;
endmodule
