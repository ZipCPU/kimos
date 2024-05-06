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
		output	reg		o_sync, o_repeat_stb, o_null_pkt,
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
	reg	[15:0]	pktlen;
	reg	[5:0]	addr;
	reg		nomatch, drop, r_syncd;
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

	// addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		addr    <= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (pktlen > 4 || (addr == 0 && S_AXI_TDATA[15:0] > 4))
		begin
			if (!addr[5])
				addr <= addr + 1;
		end else
			addr <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert((addr == 0) == (pktlen == 0));
`endif
	// }}}

	// pktlen
	// {{{
	initial	pktlen = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		pktlen	<= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (addr == 0)
			pktlen <= (S_AXI_TDATA[15:0] > 4) ? (S_AXI_TDATA[15:0] - 4) : 0;
		else if (pktlen <= 4)
			pktlen <= 0;
		else
			pktlen <= pktlen - 4;
	end
	// }}}

	// o_null_pkt
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !r_syncd)
		o_null_pkt    <= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY && addr == 10 && !nomatch
				&& r_syncd
				&& S_AXI_TDATA[31:16] != o_host_frameid
				&& S_AXI_TDATA[31:16] != 0)
		o_null_pkt <= (pktlen == 4) && (!i_handler_busy)
				&& !word_valid && !m_valid;
	else
		o_null_pkt <= 1'b0;
	// }}}

	initial	word_valid = 1'b0;
	initial	word_last  = 4'b0;
	initial	o_gpio     = DEF_GPIO;
	initial	o_repeat_stb  = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		nomatch <= 0;
		o_gpio  <= DEF_GPIO;
		o_repeat_stb  <= 1'b0;
		// }}}
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		o_gpio <= o_gpio & ~GPIO_AUTO_CLEAR;
		o_repeat_stb <= 0;

		case(addr)
		0: begin // Capture the packet length
			// {{{
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
				if (!i_handler_busy && !word_valid && !m_valid)
				begin
					o_host_mac <= tmp_mac;
					o_host_ip <= tmp_ip;
					o_host_udpport <= tmp_sport;
					o_host_frameid <= S_AXI_TDATA[31:16];
				end

				if (S_AXI_TDATA[31:16] == 0)
					drop <= 1;
				if (OPT_REPEAT_SUPPRESSION
					&& S_AXI_TDATA[31:16]== o_host_frameid
					&& o_host_frameid != 0)
				begin
					drop <= 1;
					o_repeat_stb <= 1'b1;
				end

				if (i_handler_busy || m_valid || word_valid || !r_syncd)
					{ drop, o_repeat_stb } <= 2'b10;

				o_gpio <= (o_gpio & ~(S_AXI_TDATA[15:8]
						| GPIO_AUTO_CLEAR))
					| (S_AXI_TDATA[15:8]& S_AXI_TDATA[7:0]);
			end end
			// }}}
		default: begin // Process (or skip) the payload data
			// {{{
			if (pktlen <= 4)
			begin
				nomatch <= 0;
				drop    <= 0;
			end end
			// }}}
		endcase
	end else begin
		o_repeat_stb <= 0;
	end

	initial	word_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		word_valid <= 0;
		word_last  <= 4'h0;
		word_data  <= 0;
		// }}}
	end else if (!word_valid || word_ready)
	begin
		word_valid <= 0;
		word_last  <= 4'h0;

		if (addr > 10 && !drop)
		begin
			word_valid <= S_AXI_TVALID && S_AXI_TREADY;
			word_data  <= S_AXI_TDATA;
			word_last[3] <= (pktlen == 1) && S_AXI_TVALID && S_AXI_TREADY;
			word_last[2] <= (pktlen == 2) && S_AXI_TVALID && S_AXI_TREADY;
			word_last[1] <= (pktlen == 3) && S_AXI_TVALID && S_AXI_TREADY;
			word_last[0] <= (pktlen == 4) && S_AXI_TVALID && S_AXI_TREADY;
		end
	end

	// On entrance, we know this packet is to us, its to our IP address,
	// its a UDP packet, and its to our UDP port.  Now we need to know
	// if it is a synch packet:
	// 1. It must have a frame ID of zero.
	initial	o_sync  = 1'b0;
	initial	r_syncd = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		o_sync <= 0;
		r_syncd <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY && (addr == 10)
			&& (S_AXI_TDATA[31:16] == 0) && !i_handler_busy)
	begin
		o_sync <= 1'b1;
		r_syncd <= 1'b1;
	end else
		o_sync <= 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #2: Break the incoming words into bytes for the payload handler
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	new_load = ~(word_last - 1);

	initial	m_valid = 0;
	initial	m_loaded = 0;
	initial m_last   = 0;
	initial	m_data   = 0;
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
		// Step everything forward by one byte by default
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
`ifdef	FORMAL
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $rose(word_valid && (word_last != 0)))
		assert(addr == 0);
`endif
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
	reg	[15:0]	fs_len, fw_len;
	reg	[16:0]	fs_len_words;
	(* keep *) reg	[15:0]	fs_word, fs_byte;
	reg	[17:0]	fm_word;
	reg	[16:0]	fs_calc, fw_calc;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);
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
		fs_len_words = { 1'b0, fs_len } + 3;
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

		if (fs_word != 0 && (fs_word + 1 >= fs_len_words))
			fs_word <= 0;
		if (fs_word == 0 && S_AXI_TDATA[15:0] <= 4)
			fs_word <= 0;
	end

	always @(*)
		fs_byte = fs_word << 2;

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assert(!M_AXI_TVALID);
	else if ($past(M_AXI_TVALID && !M_AXI_TREADY))
	begin
		assert(M_AXI_TVALID);
		assert($stable(M_AXI_TDATA));
		assert($stable(M_AXI_TLAST));
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && addr != 0)
	begin
		assert(fs_word + pktlen[15:2]
				+ (pktlen[1:0] ? 1'b1 : 1'b0) == fs_len_words);
		assert({ fs_word, 2'b00 } + pktlen == fs_len);

		if (pktlen > 0)
			assert(pktlen[1:0] == fs_len[1:0]);
		/*
		case(fs_len[1:0])
		2'b00: assert(word_last[3:1] == 0);
		2'b01: assert(word_last[2:0] == 0);
		2'b10: assert(word_last[1:0] == 0 && word_last[3:3] == 0);
		2'b11: assert(word_last[0:0] == 0 && word_last[3:2] == 0);
		endcase
		*/
		if (addr > 10 && !drop)
			assert(word_last == 0);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && word_valid)
	begin
		if (word_last != 0)
			assert(addr < 11 || drop);

		case(word_last)
		4'h0: begin end
		4'h1: begin end
		4'h2: begin end
		4'h4: begin end
		4'h8: begin end
		default: assert(1'b0);
		endcase
	end else if (S_AXI_ARESETN)
		assert(word_last == 0);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && m_valid)
	begin
		if (m_last != 0)
			assert(addr < 11 || drop);

		case(m_last)
		4'h0: begin end
		4'h1: begin end
		4'h2: begin end
		4'h4: begin end
		4'h8: begin end
		default: assert(1'b0);
		endcase
	end else if (S_AXI_ARESETN)
		assert(m_last == 0);

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

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assert(!word_valid);
	else if ($past(word_valid && !word_ready))
	begin
		assert(word_valid);
		assert($stable(word_data));
		assert($stable(word_last));
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (m_loaded != 0)
			assert(m_valid);
		case(m_loaded)
		3'b000: begin end
		3'b100: begin end
		3'b110: begin end
		3'b111: begin end
		default: assert(0);
		endcase

		if (m_last[2:0] != 0)
		begin
			assert((m_last & m_loaded) != 0);
			assert(((m_last[2:0] -1)& m_loaded) == 0);
		end

		if (m_last[3])
		begin
			assert(m_last[2:0] == 3'b0);
			assert(m_loaded[2:0] == 3'b0);
		end
	end

	always @(*)
	begin
		fw_calc = fm_word + (m_valid ? 1:0)
				+ (m_loaded[2] ? 1:0)
				+ (m_loaded[1] ? 1:0)
				+ (m_loaded[0] ? 1:0)
				+ 44;

		if (word_valid)
		case(word_last)
		4'h0: fs_calc = fw_calc + 4;
		4'h1: fs_calc = fw_calc + 4;
		4'h2: fs_calc = fw_calc + 3;
		4'h4: fs_calc = fw_calc + 2;
		4'h8: fs_calc = fw_calc + 1;
		default: begin end	
		endcase
		else
			fs_calc = fw_calc;
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assert(fm_word <= 18'h0ffff - 18'd44);
		assert(fs_calc <= 18'h0ffff);

		if(m_valid && m_last != 0)
			assert(!word_valid);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && addr > 10 && !drop && fs_word != 0 && word_last == 0)
	begin
		assert(fs_calc[1:0] == 2'b00);
		assert(fs_calc[16:2] == fs_word);
		assert(fm_word <= { fs_word, 2'b00 });

		assert(!M_AXI_TLAST);
		assert(m_last == 0);
		assert(word_last == 0);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && (addr < 11 || drop))
	begin
		if (word_valid)
			assert(word_last != 0 && m_last == 0);
		else if (m_valid)
			assert(m_last != 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Handler
	// {{{

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assume(!i_handler_busy);
	else if ($past(M_AXI_TVALID && M_AXI_TREADY))
		assume(i_handler_busy);
	else
		assume(!$rose(i_handler_busy));

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && fm_word > 0)
		assume(i_handler_busy);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && (i_handler_busy || word_valid || m_valid))
	begin
		assert($stable(o_host_mac));
		assert($stable(o_host_ip));
		assert($stable(o_host_udpport));
		assert($stable(o_host_frameid));
		assert(r_syncd);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{
	(* anyconst *)	reg		fc_check, fc_repeat, fc_last;
	// (* anyconst *)	reg		fc_sync;
	(* anyconst *)	reg	[15:0]	fc_index;
			reg	[15:0]	fcs_index, fcm_index;
	(* anyconst *)	reg	[31:0]	fc_data;
			reg	[31:0]	fsub_data;

	always @(posedge S_AXI_ACLK)
	if (fc_check && S_AXI_TVALID && addr == 0)
	begin
		if (fc_last)
			assume(S_AXI_TDATA[15:0] == fc_index + 1);
		else
			assume(S_AXI_TDATA[15:0] > fc_index + 1);
	end

	always @(*)
	if (S_AXI_ARESETN && fc_check && addr > 0)
	begin
		if (fc_last)
			assert(fs_len == fc_index + 1);
		else
			assert(fs_len > fc_index + 1);
	end

	// always @(posedge S_AXI_ACLK)
	// if (fc_check && S_AXI_TVALID && addr == 10)
	// begin
		// assume(fc_sync == (S_AXI_TDATA[31:16] == 0));
	// end

	// always @(posedge S_AXI_ACLK)
	// if (fc_check && fc_sync && addr > 0)
	//	assume(fs_len == 40);

	// always @(*)
	// if (S_AXI_ARESETN && fc_check && !fc_sync)
		// assert(!o_sync);

	always @(*)
	begin
		// fcs_index = fc_index  +  3;
		fcs_index = fc_index >> 2;
		fcm_index = fc_index  - 44;
	end

	always @(posedge S_AXI_ACLK)
	if (fc_check && S_AXI_TVALID && fs_word == fcs_index)
		assume(S_AXI_TDATA == fc_data);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && o_repeat_stb)
		assert(drop && o_host_frameid != 0);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && addr > 10 && nomatch)
		assert(drop);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		assert(addr <= 6'h20);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (!addr[5])
			assert(addr == fs_word);
		else
			assert(fs_word >= addr);
	end

	//
	// word_* section
	//

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (fw_calc >= fw_len)
		begin
			assert(!word_valid);
		end

		if (M_AXI_TVALID)
		begin
			assert(fm_word + 1 + (M_AXI_TLAST ? 0:1) <= fw_len);
		end
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && fc_check && word_valid && fw_calc[15:2] == fcs_index)
	begin
		assert(word_data == fc_data);
		// assert(fc_last == (word_last != 0));

		cover(1'b1);

		if (fc_last)
		case(fw_len[1:0])
		2'b00: begin assert(word_last == 4'h1); cover(1'b1); end // !!!
		2'b01: begin assert(word_last == 4'h8); cover(1'b1); end // !!!
		2'b10: begin assert(word_last == 4'h4); cover(1'b1); end // !!!
		2'b11: begin assert(word_last == 4'h2); cover(1'b1); end // !!!
		endcase
		else case(fw_len[1:0])
		2'b00: begin assert(word_last == 4'h1 || word_last == 4'h0); end
		2'b01: begin assert(word_last == 4'h0); end
		2'b10: begin assert(word_last == 4'h4 || word_last == 4'h0); end
		2'b11: begin assert(word_last != 4'h1); end
		endcase

		// assert(M_AXI_TLAST == fc_last);
	end

	always @(*)
	if (S_AXI_ARESETN && word_valid)
		assert(r_syncd);

	always @(*)
	if (S_AXI_ARESETN && addr > 10 && !drop)
		assert(r_syncd);

	initial	fw_len = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fw_len <= 0;
	else if (addr == 10 && !nomatch && S_AXI_TDATA[31:16] != 0
			&& !i_handler_busy && !word_valid && !m_valid)
		fw_len <= fs_len;

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && addr > 10 && !drop)
		assert(fs_len == fw_len);

	always @(*)
	if (S_AXI_ARESETN && word_valid)
	begin
		if (fw_calc + 4 < fw_len)
		begin
			assert(word_last == 0);
		end else if (fw_calc + 4 == fw_len)
		begin
			assert(word_last == 4'h1);
		end else if (fw_calc + 3 == fw_len)
		begin
			assert(word_last == 4'h2);
		end else if (fw_calc + 2 == fw_len)
		begin
			assert(word_last == 4'h4);
		end else if (fw_calc + 1 == fw_len)
		begin
			assert(word_last == 4'h8);
		end else if (fw_calc + 0 == fw_len)
		begin
			assert(0);
		end
	end else if (S_AXI_ARESETN && fw_calc < fw_len && fw_calc > 44)
	begin
		assert(!drop && addr > 10);
	end

	always @(*)
	if (S_AXI_ARESETN && fc_check && ((addr > 10 && !drop)
					||word_valid || m_valid))
	begin
		if (fc_last)
			assert(fw_len == fc_index + 1);
		else
			assert(fw_len > fc_index + 1);
	end


	//
	// m_* section
	//

	always @(*)
		fsub_data = fc_data << (fm_word[1:0]*8);

	always @(posedge S_AXI_ACLK)
	if (fc_check && M_AXI_TVALID && fcs_index > 10)
	begin
		if (fm_word == fcm_index)
		begin
			assert(M_AXI_TDATA == fsub_data[31:24]);
			assert(M_AXI_TLAST == fc_last);
		end else if (fm_word + 1 == fcm_index && m_loaded[2])
		begin
			assert(m_data[23:16] == fsub_data[23:16]);
			assert(m_last[2] == fc_last);
		end else if (fm_word + 2 == fcm_index && m_loaded[1])
		begin
			assert(m_data[15:8] == fsub_data[15:8]);
			assert(m_last[1] == fc_last);
		end else if (fm_word + 3 == fcm_index && m_loaded[0])
		begin
			assert(m_data[7:0] == fsub_data[7:0]);
			assert(m_last[0] == fc_last);
		end

		if (m_valid)
		case(fm_word[1:0])
		2'b00: begin end //
		2'b01: assert(m_loaded[  0] == 1'h0 && m_data[ 7:0] ==  8'h0);
		2'b10: assert(m_loaded[1:0] == 2'h0 && m_data[15:0] == 16'h0);
		2'b11: assert(m_loaded      == 3'h0 && m_data[23:0] == 24'h0);
		endcase

		if (m_valid && m_last == 0 && !M_AXI_TLAST)
		case(fm_word[1:0])
		2'b00: assert(m_loaded == 3'h7);
		2'b01: assert(m_loaded == 3'h6);
		2'b10: assert(m_loaded == 3'h4);
		2'b11: assert(m_loaded == 3'h0);
		endcase
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && m_valid && fc_check && fcs_index > 10)
	begin
		if (fm_word == fcm_index)
		begin
			assert(m_last[3] == fc_last);
		end else if (fm_word + 1 == fcm_index
				&& (m_loaded[2] || fcm_index[1:0] != 0))
		begin
			assert((m_last[2] == fc_last) && m_loaded[2]);
		end else if (fm_word + 2 == fcm_index
				&& (m_loaded[1] || fcm_index[1:0] > 1))
		begin
			assert((m_last[1] == fc_last) && m_loaded[1]);
		end else if (fm_word + 3 == fcm_index
				&& (m_loaded[0] || fcm_index[1:0] > 2))
		begin
			assert((m_last[0] == fc_last) && m_loaded[0]);
		end
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && m_valid) // && fm_index == fw_len)
	begin
		if (fm_word + 1 == fw_len)
		begin
			assert(m_last[3]);
		end else if (fm_word + 2 == fw_len && m_loaded[2])
		begin
			assert(m_last[2]);
		end else if (fm_word + 3 == fw_len && m_loaded[1])
		begin
			assert(m_last[1]);
		end else if (fm_word + 4 == fw_len && m_loaded[0])
		begin
			assert(m_last[0]);
		end
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && m_valid && fc_check && addr > 10 && !drop && fs_word < fcs_index)
		assert(m_last == 0 && word_last == 0);

	always @(*)
	if (S_AXI_ARESETN && m_valid)
		assert(r_syncd);


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		cover(S_AXI_TVALID && addr == 10 && S_AXI_TDATA[15:0] == 0); // Step 13
	end

	// always @(posedge S_AXI_ACLK)
	// if (S_AXI_ARESETN)
	//	cover(fc_sync && o_sync);		// Step 14

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		cover(M_AXI_TVALID && M_AXI_TLAST);	// Step 27

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		cover(o_repeat_stb);			// Step 36
		cover(o_null_pkt);			// Step 25
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && fc_check)
	begin
		cover(fcs_index == 12 && fm_word == fcm_index); // !!!!
		cover(fcs_index >= 12 && fm_word == fcm_index); // !!!!
		cover(fm_word > 0 && fm_word == fcm_index);

		cover(r_syncd);
		cover(r_syncd && !drop && addr > 1);
		cover(r_syncd && !drop && addr > 5);
		cover(r_syncd && !drop && addr > 8);

		cover(M_AXI_TVALID);
		cover(M_AXI_TVALID && fcs_index == 11);
		cover(M_AXI_TVALID && fcs_index == 12);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && fc_check && M_AXI_TVALID
				&& fcs_index > 11 && fm_word == fcm_index)
	begin
		cover(fc_last);		// !!!
		cover(!fc_last);		// !!!
		case(fm_word[1:0])
		2'b00: cover(1'b1);		// !!!
		2'b01: cover(1'b1);		// !!!
		2'b10: cover(1'b1);		// !!!
		2'b11: cover(1'b1);		// !!!
		endcase
	end


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	// }}}
`endif
// }}}
endmodule
