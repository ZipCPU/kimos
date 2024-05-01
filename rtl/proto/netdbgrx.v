////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/netdbgrx.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	First stage processing of a network debugging packet.  Handles
//		synchronization, repeat detection, and GPIO outputs.
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
// }}}
module	netdbgrx #(
		parameter [7:0]	GPIO_AUTO_CLEAR = 8'h7,
		parameter [7:0]	DEF_GPIO = 8'h0,
		parameter [0:0]	OPT_REPEAT_SUPPRESSION = 1'b1
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		// Incoming interface
		// {{{
		input	wire		S_AXI_TVALID,
		output	wire		S_AXI_TREADY,
		input	wire [31:0]	S_AXI_TDATA,
		// No S_AXI_TLAST.  Packet size is captured by the first word
		// in the packet
		// }}}
		// Outgoing GPIO registers
		// {{{
		output	reg	[7:0]	o_gpio,
		// }}}
		// Outgoing interface
		// {{{
		output	reg		o_sync, o_repeat_stb,
		output	reg	[47:0]	o_host_mac,
		output	reg	[31:0]	o_host_ip,
		output	reg	[15:0]	o_host_udpport,
		output	reg	[15:0]	o_host_frameid,
		//
		input	wire		i_handler_busy,
		// }}}
		// Payload interface
		// {{{
		output	wire		M_AXI_TVALID,
		input	wire		M_AXI_TREADY,
		output	wire	[7:0]	M_AXI_TDATA,
		output	wire		M_AXI_TLAST,
		// }}}
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	reg	[15:0]	pktlen, addr;
	reg		nomatch, drop;
	reg		word_valid;
	reg	[31:0]	word_data;
	reg	[3:0]	word_last;

	reg	[47:0]	tmp_mac;
	reg	[31:0]	tmp_ip;
	reg	[15:0]	tmp_sport;

	wire		word_ready;

	reg		m_valid;
	reg	[31:0]	m_data;
	reg	[2:0]	m_loaded;
	reg	[3:0]	m_last;
	wire	[3:0]	new_load;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #1: Process the incoming packet
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	S_AXI_TREADY = (addr < 10)|| drop ||(!word_valid || word_ready);
	assign	word_ready = (!M_AXI_TVALID ||(M_AXI_TREADY && !m_loaded[2]));

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		nomatch <= 0;
		o_gpio  <= DEF_GPIO;
		addr    <= 0;
		word_valid <= 0;
		word_last  <= 4'h0;
		// }}}
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		o_gpio <= o_gpio & ~GPIO_AUTO_CLEAR;
		word_valid <= 0;
		word_last  <= 4'h0;
		if (pktlen >= 4)
			pktlen <= pktlen - 4;
		else
			pktlen <= 0;
		addr <= addr + 1;
		o_repeat_stb <= 0;

		case(addr)
		0: begin // Capture the packet length
			// {{{
			pktlen <= 0;
			if (S_AXI_TDATA[15:0] > 4)
				pktlen <= S_AXI_TDATA[15:0]-4;
			nomatch <= 0;
			drop <= 0;
			end
			// }}}
		1: begin // Match the source MAC address
			// {{{
			if (S_AXI_TDATA != o_host_mac[47:16])
			begin
				tmp_mac[47:16] <= S_AXI_TDATA;
				nomatch <= 1;
			end end
			// }}}
		2: begin // Match the second half of the source MAC address
			// {{{
			if (S_AXI_TDATA[31:16] != o_host_mac[15:0])
			begin
				tmp_mac[15:0] <= S_AXI_TDATA[31:16];
				nomatch <= 1;
			end end
			// }}}
		6: begin // Match source IP address
			// {{{
			if (S_AXI_TDATA != o_host_ip[31:0])
			begin
				tmp_ip <= S_AXI_TDATA;
				nomatch <= 1;
			end end
			// }}}
		8: begin // Match source UDP port
			// {{{
			if (S_AXI_TDATA[31:16] != o_host_udpport[15:0])
			begin
				tmp_sport <= S_AXI_TDATA[31:16];
				nomatch <= 1;
			end end
			// }}}
		10: begin // Sync on new frame
			// {{{
			if (S_AXI_TDATA[31:16] != 0 && nomatch)
				drop <= 1;
			else begin
				if (!i_handler_busy)
				begin
					o_host_mac <= tmp_mac;
					o_host_ip <= tmp_ip;
					o_host_udpport <= tmp_sport;
					o_host_frameid <= S_AXI_TDATA[31:16];
				end

				drop <= i_handler_busy;
				if (OPT_REPEAT_SUPPRESSION
					&& S_AXI_TDATA[31:16]== o_host_frameid
					&& o_host_frameid != 0)
				begin
					drop <= 1;
					o_repeat_stb <= 1'b1;
				end
				if (i_handler_busy)
					o_repeat_stb <= 1'b0;

				o_gpio <= (o_gpio & ~(S_AXI_TDATA[15:8]
						| GPIO_AUTO_CLEAR))
					| (S_AXI_TDATA[15:8]& S_AXI_TDATA[7:0]);
			end end
			// }}}
		default: begin // Process (or skip) the payload data
			// {{{
			word_last <= 0;

			if (pktlen <= 4)
			begin
				addr    <= 0;
				nomatch <= 0;
				drop    <= 0;
			end

			if (addr >= 11)
			begin
				word_valid <= !drop;
				word_data  <= S_AXI_TDATA;
				word_last[3] <= (pktlen == 1);
				word_last[2] <= (pktlen == 2);
				word_last[1] <= (pktlen == 3);
				word_last[0] <= (pktlen == 4);
			end end
			// }}}
		endcase
	end else begin
		if (word_ready)
			word_valid <= 0;
		o_repeat_stb <= 0;
		if (pktlen == 0)
			addr <= 0;
	end

	// On entrance, we know this packet is to us, its to our IP address,
	// its a UDP packet, and its to our UDP port.  Now we need to know
	// if it is a synch packet:
	// 1. It must have a frame ID of zero.
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_sync <= 0;
	else
		o_sync <= S_AXI_TVALID && S_AXI_TREADY && (addr == 10)
			&& (S_AXI_TDATA[31:16] == 0) && !i_handler_busy;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #2: Break the incoming words into bytes for the payload handler
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	new_load = ~(word_last - 1);

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		m_valid  <= 0;
		m_loaded <= 0;
		m_last   <= 0;
		m_data   <= 0;
		// }}}
	end else if (!M_AXI_TVALID || M_AXI_TREADY)
	begin
		// {{{
		m_loaded <= { m_loaded[1:0], 1'b0 };
		m_last   <= { m_last[2:0],   1'b0 };
		m_data   <= { m_data[23:0],  8'b0 };

		if (!m_loaded[2])
		begin
			m_valid <= word_valid;
			m_data <= word_data;
			if (word_last == 0)
				m_loaded  <= 3'h7;
			else
				m_loaded <= new_load[2:0];
			if (!word_valid)
				m_loaded <= 0;
			m_last <= word_last;
		end else
			m_valid <= m_loaded[2];
		// }}}
	end

	assign	M_AXI_TVALID = m_valid;
	assign	M_AXI_TDATA  = m_data[31:24];
	assign	M_AXI_TLAST  = m_last[3];
	// }}}

	assign	o_debug = {
			S_AXI_TVALID,
			M_AXI_TVALID, o_sync,
			nomatch, drop, i_handler_busy,

			S_AXI_TVALID, S_AXI_TREADY, m_loaded[2:0],
				addr[4:0], S_AXI_TDATA[15:0]
			};

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, new_load[3] };
	// Verilator lint_on  UNUSED
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
	reg	f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assert(!S_AXI_ARESETN);
	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assume(!S_AXI_TVALID);
	else if ($past(S_AXI_TVALID && !S_AXI_TREADY))
	begin
		assume(S_AXI_TVALID);
		assume($stable(S_AXI_TDATA));
	end

	always @(*)
	begin
		fs_len_words = fs_len + 3;
		fs_len_words = fs_len_words >> 2;
	end

	initial	fs_word = 0;
	initial	fs_len  = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		fs_word <= 0;
		fs_len  <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (fs_word == 0)
			fs_len <= S_AXI_TDATA[15:0];
		fs_word <= fs_word + 1;

		if (fs_word + 1 >= fs_len_words[15:2])
			fs_word = 0;
	end

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assert(!M_AXI_TVALID);
	else if ($past(M_AXI_TVALID && !M_AXI_TREADY))
	begin
		assert(M_AXI_TVALID);
		assert($stable(M_AXI_TDATA));
		assert($stable(M_AXI_TLAST));
	end

	initial	fm_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fm_word <= 0;
	else if (M_AXI_TVALID && M_AXI_TREADY)
	begin
		fm_word <= fm_word + 1;
		if (M_AXI_TLAST)
			fm_word <= 0;
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	(* anyconst *)	reg		fc_check;
	(* anyconst *)	reg	[13:0]	fc_index;
	(* anyconst *)	reg	[31:0]	fc_data;
	reg	[7:0]	fsub_data;

	always @(posedge S_AXI_ACLK)
	if (fc_check && S_AXI_TVALID && fs_word == fc_index)
		assume(S_AXI_TDATA == fc_data);

	always @(*)
		fsub_data = fc_data >> (fm_word*8);

	// always @(posedge S_AXI_ACLK)
	// if (fc_check && M_AXI_TVALID && fc_index > 11 && fm_word[15:2] == fc_index - 11)
	//	assert(M_AXI_TDATA == fc_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	// }}}
`endif
// }}}
endmodule
