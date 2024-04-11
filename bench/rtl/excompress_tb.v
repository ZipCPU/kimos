////////////////////////////////////////////////////////////////////////////////
//
// Filename:	bench/rtl/excompress_tb.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	This file exists to provide a quick VCD which can be used to
//		visualize the operation of the ExBus compression stage.
//	Specifically, we're focused here on the table lookup portion of that
//	compression.
//
//	This is *NOT* a "proper" test bench.  It is not self-checking.  Indeed,
//	the only checking provided by this test bench is the checking that takes
//	place by eye when viewing the result.  Still, it's been useful to me,
//	and so I'm leaving it as part of the repository (for now).
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
`default_nettype none
`timescale 1ns/100ps
// }}}
module excompress_tb;
	// Local declarations
	// {{{
	reg		clk, reset;

	reg		instb,  outbusy;
	wire		outstb, inbusy, active;
	reg	[34:0]	inword;
	wire	[34:0]	outword;
	integer		chkidx;
	reg	[31:0]	chktbl	[0:511];
	reg	[9:0]	bsycount;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock and reset
	// {{{
	initial	clk = 1'b0;
	always
		#5 clk = !clk;

	initial begin
		reset = 1;
		@(posedge clk)
			reset <= 0;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// VCD generation
	// {{{
	initial
	begin
		$dumpfile("excompress_tb.vcd");
		$dumpvars(0, excompress_tb);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Test script
	// {{{
	// This is quick and dirty, and rather lacks focus.  A more thorough
	// test is available via excheck.cpp.  This just allows testing from
	// a Verilog only standpoint.
	initial begin
		chkidx = 0;
		instb  = 0;
		for(chkidx = 0; chkidx < 512; chkidx = chkidx + 1)
			chktbl[chkidx] = $random;

		wait(!reset);

		@(posedge clk)
		begin
			instb   <= 1'b0;
		end

		@(posedge clk)
		begin
			instb  <= 1'b1;
			inword <= { 2'b00, 1'b0, 32'h0a00_0000 };
			chkidx <= 0;
		end @(negedge clk);

		while(chkidx != 520)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b01, 1'b0, chktbl[chkidx[8:0]] };
				chkidx <= chkidx + 1;
			end
		end @(negedge clk);

		chkidx = 0;

		while(chkidx[8:0] != 1)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b01, 1'b0, chktbl[chkidx[8:0]] };
				chkidx <= chkidx + 1;
			end
		end @(negedge clk)

		while(chkidx < 8)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b01, 1'b0, 32'h0 };
				inword[31:0] <= $random;
				chkidx <= chkidx + 1;
			end
		end

		while(chkidx < 12)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b01, 1'b0, 32'h0 };
				inword[31:0] <= chktbl[9'd10];
				chkidx <= chkidx + 1;
			end
		end

		while(chkidx < 13)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b00, 1'b0, 32'h0a80_0000 };
				chkidx <= chkidx + 1;
			end
		end

		while(chkidx < 17)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b01, 1'b0, 32'h0a80_0000 };
				inword[31:0] <= chktbl[9'd10];
				chkidx <= chkidx + 1;
			end
		end

		while(chkidx < 40)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
			begin
				instb <= 1'b1;
				inword <= { 2'b01, 1'b0, 32'h0a80_0000 };
				inword[31:0] <= chktbl[{ 6'h0, chkidx[2:0] }];
				chkidx <= chkidx + 1;
			end
		end

		while(instb)
		begin
			@(posedge clk)
			if (!instb || !inbusy)
				instb <= 1'b0;
		end

		while(outstb || active)
			@(posedge clk);

		$finish;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate the busy/backpressure
	// {{{
	// This is based upon a presumed 1MBaud serial port operating from a
	// 100MHz clock.  As a result, the outbound link will only accept one
	// 35-bit word every 1k clock cycles.  Of course, even this is
	// unrealistic, because those 35-bits would need to be sent out over
	// between 1 and 5 characters, but ... it's good enough for today's
	// debugging purposes since it forces the compression algorithm to go
	// through all of its paces.
	always @(posedge clk)
	if (reset)
		bsycount <= 0;
	else if (outstb && !outbusy)
		bsycount <= 1000;
	else if (bsycount > 0)
		bsycount <= bsycount - 1;

	always @(*)
		outbusy = (bsycount > 0);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The device under test: excompress
	// {{{
	excompress
	u_dut (
		.i_clk(clk), .i_reset(reset),
		.i_stb(instb), .i_word(inword), .o_busy(inbusy),
		.o_stb(outstb), .o_word(outword), .i_busy(outbusy),
		.o_active(active)
	);
	// }}}
endmodule
