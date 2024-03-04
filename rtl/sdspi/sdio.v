////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/sdspi/sdio.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	Top level module (minus the front end) for the SDIO controller.
//		Contains submodules, but very little logic.
//
// Submodules:
//	sdwb:		Wishbone bus handler.  Also includes FIFO memory.
//	sdckgen:	Digital clock divider
//	sdcmd:		Request commands, process responses
//	sdrxframe:	Process receive frames into memory writes
//	sdtxframe:	Process memory reads into frames to transmit
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
`timescale 1ns/1ps
`default_nettype	none
// }}}
module	sdio #(
		// {{{
		parameter	LGFIFO = 15,//	= log_2(FIFO size in bytes)
				NUMIO=4,
		parameter	MW = 32,
		parameter [0:0]	OPT_DMA = 1'b0,
		parameter	ADDRESS_WIDTH = 30,
		parameter	DMA_DW = 32,	// DMA bus width
		// DMA_AW: The DMA address connection width
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter	DMA_AW = ADDRESS_WIDTH-$clog2(DMA_DW/8),
		// To support more than one bit of IO per clock, we need
		//  serdes support.  Setting OPT_SERDES to zero will disable
		//  that support, effectively limiting our operation to 50MHz
		//  from a 100MHz clock.
		parameter [0:0]	OPT_SERDES = 1'b0,
		parameter [0:0]	OPT_DDR = 1'b0,
		parameter [0:0]	OPT_DS  = OPT_SERDES,
		parameter [0:0]	OPT_1P8V= 1'b0,
		parameter [0:0]	OPT_EMMC = 1'b1,
		parameter [0:0]	OPT_CARD_DETECT = !OPT_EMMC,
		parameter	LGTIMEOUT = 23,
		parameter [0:0]	OPT_ISTREAM = 0, OPT_OSTREAM = 0,
		parameter	SW = 32
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Control interface
		// {{{
		// Control (Wishbone) interface
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[2:0]	i_wb_addr,
		input	wire [MW-1:0]	i_wb_data,
		input	wire [MW/8-1:0]	i_wb_sel,
		//
		output	wire		o_wb_stall, o_wb_ack,
		output	wire [MW-1:0]	o_wb_data,
		// }}}
		// }}}
		// DMA interface
		// {{{
		// DMA (Wishbone) interface
		// {{{
		output	wire			o_dma_cyc, o_dma_stb, o_dma_we,
		output	wire [DMA_AW-1:0]	o_dma_addr,
		output	wire [DMA_DW-1:0]	o_dma_data,
		output	wire [DMA_DW/8-1:0]	o_dma_sel,
		//
		input	wire			i_dma_stall, i_dma_ack,
		input	wire [DMA_DW-1:0]	i_dma_data,
		input	wire			i_dma_err,
		// }}}
		// }}}
		// External stream interface
		// {{{
		input	wire			s_valid,
		output	wire			s_ready,
		input	wire	[SW-1:0]	s_data,

		output	wire			m_valid,
		input	wire			m_ready,
		output	wire	[SW-1:0]	m_data,
		output	wire			m_last,
		// }}}
		input	wire		i_card_detect,
		output	wire		o_1p8v,
		output	wire		o_int,
		// Interface to PHY
		// {{{
		// Not these wires--those will be the connections handled by
		// the PHY
		// inout	wire		io_cmd,
		// inout	wire		io_ds,
		// inout wire [NUMIO-1:0]	io_dat,
		// But these ones ...
		output	wire		o_cfg_ddr, o_cfg_ds, o_cfg_dscmd,
		output	wire	[4:0]	o_cfg_sample_shift,
		output	reg	[7:0]	o_sdclk,
		//
		output	wire		o_cmd_en, o_pp_cmd,
		output	wire	[1:0]	o_cmd_data,
		//
		output	wire		o_data_en, o_pp_data, o_rx_en,
		output	wire	[31:0]	o_tx_data,
		//
		input	wire	[1:0]	i_cmd_strb, i_cmd_data,
		input	wire		i_cmd_collision,
		input	wire		i_card_busy,
		input	wire	[1:0]	i_rx_strb,
		input	wire	[15:0]	i_rx_data,
		//
		input	wire		S_AC_VALID,
		input	wire	[1:0]	S_AC_DATA,
		input	wire		S_AD_VALID,
		input	wire	[31:0]	S_AD_DATA
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	wire			soft_reset;

	wire			cfg_clk90, cfg_clk_shutdown;
	wire	[7:0]		cfg_ckspeed;
	wire	[1:0]		cfg_width;

	wire			clk_stb, clk_half;
	wire	[7:0]		w_sdclk, clk_ckspd;

	wire			cmd_request, cmd_err, cmd_busy, cmd_done;
	wire			cmd_selfreply;
	wire	[1:0]		cmd_type, cmd_ercode;
	wire			rsp_stb;
	wire	[6:0]		cmd_id;
	wire	[5:0]		rsp_id;
	wire	[31:0]		cmd_arg, rsp_arg;
	wire			cmd_mem_valid;
	wire	[MW/8-1:0]	cmd_mem_strb;
	wire	[LGFIFO-$clog2(MW/8)-1:0]	cmd_mem_addr;
	wire	[MW-1:0]	cmd_mem_data;

	wire			tx_en, tx_mem_valid, tx_mem_ready, tx_mem_last;
	wire	[31:0]		tx_mem_data;

	wire			crc_en;
	wire	[LGFIFO:0]	rx_length;
	wire			rx_mem_valid;
	wire	[LGFIFO-$clog2(MW/8)-1:0]	rx_mem_addr;
	wire	[MW/8-1:0]	rx_mem_strb;
	wire	[MW-1:0]	rx_mem_data;
	wire			rx_done, rx_err, rx_ercode, rx_active, rx_en;

	// DMA declarations
	// {{{
	wire		dma_sd2s, sd2s_valid, sd2s_ready, sd2s_last;
	wire	[31:0]	sd2s_data;
		//
	wire		dma_s2sd, s2sd_valid, s2sd_ready;
	wire	[31:0]	s2sd_data;
		//
	wire			dma_busy, dma_abort, dma_err;
	wire	[ADDRESS_WIDTH+((OPT_ISTREAM||OPT_OSTREAM) ? 1:0)-1:0] dma_addr;
	wire	[LGFIFO:0]	dma_len;
	// }}}
	// }}}

	sdwb #(
		// {{{
		.LGFIFO(LGFIFO), .NUMIO(NUMIO),
		.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
		.OPT_SERDES(OPT_SERDES),
		.OPT_DS(OPT_DS),
		.OPT_DDR(OPT_DDR),
		.OPT_CARD_DETECT(OPT_CARD_DETECT),
		.OPT_DMA(OPT_DMA),
		.DMA_AW(ADDRESS_WIDTH + ((OPT_ISTREAM||OPT_OSTREAM) ? 1:0)),
		.OPT_1P8V(OPT_1P8V),
		.OPT_EMMC(OPT_EMMC)
		// }}}
	) u_control (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		// Wishbone slave
		// {{{
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb),
		.i_wb_we(i_wb_we), .i_wb_addr(i_wb_addr),
		.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
		//
		.o_wb_stall(o_wb_stall), .o_wb_ack(o_wb_ack),
			.o_wb_data(o_wb_data),
		// }}}
		// Configuration options
		// {{{
		.o_cfg_clk90(cfg_clk90), .o_cfg_ckspeed(cfg_ckspeed),
		.o_cfg_shutdown(cfg_clk_shutdown),
		.o_cfg_width(cfg_width), .o_cfg_ds(o_cfg_ds),
			.o_cfg_dscmd(o_cfg_dscmd), .o_cfg_ddr(o_cfg_ddr),
		.o_pp_cmd(o_pp_cmd), .o_pp_data(o_pp_data),
		.o_cfg_sample_shift(o_cfg_sample_shift),
		.i_ckspd(clk_ckspd),
		// }}}
		.o_soft_reset(soft_reset),
		// DMA interface
		// {{{
		.o_dma_sd2s(dma_sd2s),
		.o_sd2s_valid(sd2s_valid),
		.i_sd2s_ready(sd2s_ready),
		.o_sd2s_data(sd2s_data),
		.o_sd2s_last(sd2s_last),
		//
		.o_dma_s2sd(dma_s2sd),
		.i_s2sd_valid(s2sd_valid),
		.o_s2sd_ready(s2sd_ready),
		.i_s2sd_data(s2sd_data),
		//
		.o_dma_addr(dma_addr),
		.o_dma_len(dma_len),
		.i_dma_busy(dma_busy),
		.i_dma_err(dma_err),
		.o_dma_abort(dma_abort),
		// }}}
		// CMD control interface
		// {{{
		.o_cmd_request(cmd_request), .o_cmd_type(cmd_type),
		.o_cmd_selfreply(cmd_selfreply),
		.o_cmd_id(cmd_id), .o_arg(cmd_arg),
		//
		.i_cmd_busy(cmd_busy), .i_cmd_done(cmd_done),
			.i_cmd_err(cmd_err), .i_cmd_ercode(cmd_ercode),
		//
		.i_cmd_response(rsp_stb), .i_resp(rsp_id),
			.i_arg(rsp_arg),
		//
		.i_cmd_mem_valid(cmd_mem_valid), .i_cmd_mem_strb(cmd_mem_strb),
			.i_cmd_mem_addr(cmd_mem_addr),
			.i_cmd_mem_data(cmd_mem_data),
		// }}}
		// TX interface
		// {{{
		.o_tx_en(tx_en),
		//
		.o_tx_mem_valid(tx_mem_valid),
			.i_tx_mem_ready(tx_mem_ready && tx_en),
		.o_tx_mem_data(tx_mem_data), .o_tx_mem_last(tx_mem_last),
		.i_tx_busy(o_data_en),
		// }}}
		// RX interface
		// {{{
		.o_rx_en(rx_en), .o_crc_en(crc_en), .o_length(rx_length),
		//
		.i_rx_mem_valid(rx_mem_valid), .i_rx_mem_strb(rx_mem_strb),
			.i_rx_mem_addr(rx_mem_addr),.i_rx_mem_data(rx_mem_data),
		//
		.i_rx_done(rx_done), .i_rx_err(rx_err), .i_rx_ercode(rx_ercode),
		// }}}
		.i_card_detect(i_card_detect),
		.i_card_busy(i_card_busy),
		.o_1p8v(o_1p8v),
		.o_int(o_int)
		// }}}
	);

	assign	o_rx_en = rx_en && rx_active;

	sdckgen
	u_clkgen (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_cfg_clk90(cfg_clk90), .i_cfg_ckspd(cfg_ckspeed),
		.i_cfg_shutdown(cfg_clk_shutdown && !rx_active),

		.o_ckstb(clk_stb), .o_hlfck(clk_half), .o_ckwide(w_sdclk),
		.o_ckspd(clk_ckspd)
		// }}}
	);

	sdcmd #(
		.OPT_DS(OPT_DS),
		.OPT_EMMC(OPT_EMMC),
		.MW(MW),
		.LGLEN(LGFIFO-$clog2(MW/8))
	) u_sdcmd (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || soft_reset),
		//
		.i_cfg_ds(o_cfg_dscmd), .i_cfg_dbl(cfg_ckspeed == 0),
		.i_ckstb(clk_stb),
		//
		.i_cmd_request(cmd_request), .i_cmd_type(cmd_type),
		.i_cmd_selfreply(cmd_selfreply),
		.i_cmd(cmd_id), .i_arg(cmd_arg),
		//
		.o_busy(cmd_busy), .o_done(cmd_done), .o_err(cmd_err),
			.o_ercode(cmd_ercode),
		//
		.o_cmd_en(o_cmd_en), .o_cmd_data(o_cmd_data),
		.i_cmd_strb(i_cmd_strb), .i_cmd_data(i_cmd_data),
			.i_cmd_collision(i_cmd_collision),
		.S_ASYNC_VALID(S_AC_VALID), .S_ASYNC_DATA(S_AC_DATA),
		//
		.o_cmd_response(rsp_stb), .o_resp(rsp_id),
			.o_arg(rsp_arg),
		//
		.o_mem_valid(cmd_mem_valid), .o_mem_strb(cmd_mem_strb),
			.o_mem_addr(cmd_mem_addr), .o_mem_data(cmd_mem_data)
		// }}}
	);

	sdtxframe #(
		.OPT_SERDES(OPT_SERDES || OPT_DDR)
		// .MW(MW)
	) u_txframe (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || soft_reset),
		//
		.i_cfg_spd(cfg_ckspeed),
		.i_cfg_width(cfg_width),
		.i_cfg_ddr(o_cfg_ddr),
		//
		.i_en(tx_en), .i_ckstb(clk_stb), .i_hlfck(clk_half),
		//
		.S_VALID(tx_en && tx_mem_valid), .S_READY(tx_mem_ready),
		.S_DATA(tx_mem_data), .S_LAST(tx_mem_last),
		//
		.tx_valid(o_data_en), .tx_data(o_tx_data)
		// }}}
	);

	sdrxframe #(
		// {{{
		.OPT_DS(OPT_SERDES), .NUMIO(NUMIO),
		.LGLEN(LGFIFO),
		.MW(MW),
		.LGTIMEOUT(LGTIMEOUT)
		// }}}
	) u_rxframe (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || soft_reset),
		//
		.i_cfg_ddr(o_cfg_ddr),
		.i_cfg_ds(o_cfg_ds), .i_cfg_width(cfg_width),
		.i_rx_en(rx_en), .i_crc_en(crc_en), .i_length(rx_length),
		//
		.i_rx_strb(i_rx_strb), .i_rx_data(i_rx_data),
		.S_ASYNC_VALID(S_AD_VALID), .S_ASYNC_DATA(S_AD_DATA),
		//
		.o_mem_valid(rx_mem_valid), .o_mem_strb(rx_mem_strb),
			.o_mem_addr(rx_mem_addr), .o_mem_data(rx_mem_data),
		//
		.o_done(rx_done), .o_err(rx_err), .o_ercode(rx_ercode),
		.o_active(rx_active)
		// }}}
	);

	always @(posedge i_clk)
		o_sdclk <= w_sdclk;

	////////////////////////////////////////////////////////////////////////
	//
	// DMA
	// {{{
	generate if (OPT_DMA)
	begin : GEN_DMA

		sddma #(
			// {{{
			.LGFIFO(LGFIFO),
			.ADDRESS_WIDTH(ADDRESS_WIDTH),
			.DW(DMA_DW),
			.OPT_ISTREAM(OPT_ISTREAM),
			.OPT_OSTREAM(OPT_OSTREAM),
			.OPT_LITTLE_ENDIAN(OPT_LITTLE_ENDIAN),
			.SW(SW)
			// }}}
		) u_sddma (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_soft_reset(soft_reset),
			.i_dma_sd2s(dma_sd2s), .i_dma_s2sd(dma_s2sd),
			//
			.i_dma_addr(dma_addr), .i_dma_len(dma_len),
			.o_dma_busy(dma_busy), .o_dma_err(dma_err),
			.i_dma_abort(dma_abort),
			//
			.i_sd2s_valid(sd2s_valid), .o_sd2s_ready(sd2s_ready),
			.i_sd2s_data(sd2s_data), .i_sd2s_last(sd2s_last),
			//
			.o_s2sd_valid(s2sd_valid), .i_s2sd_ready(s2sd_ready),
			.o_s2sd_data(s2sd_data),
			//
			.s_valid(s_valid), .s_ready(s_ready), .s_data(s_data),
			.m_valid(m_valid), .m_ready(m_ready), .m_data(m_data),
				.m_last(m_last),
			.o_dma_cyc(o_dma_cyc), .o_dma_stb(o_dma_stb),
				.o_dma_we(o_dma_we),
			.o_dma_addr(o_dma_addr), .o_dma_data(o_dma_data),
				.o_dma_sel(o_dma_sel),
			//
			.i_dma_stall(i_dma_stall),
			.i_dma_ack(i_dma_ack), .i_dma_data(i_dma_data),
			.i_dma_err(i_dma_err)
			// }}}
		);

	end else begin : NO_DMA
		// {{{
		assign	sd2s_ready = 1'b1;

		assign	s2sd_valid = 1'b0;
		assign	s2sd_data  = 32'h0;

		assign	s_ready = 1'b1;
		assign	m_valid = 1'b0;
		assign	m_data  = 0;
		assign	m_last  = 1'b0;

		assign	dma_busy = 1'b0;
		assign	dma_err  = 1'b0;

		// DMA interface
		// {{{
		// DMA (Wishbone) interface
		// {{{
		assign	{ o_dma_cyc, o_dma_stb, o_dma_we } = 3'b0;
		assign	o_dma_addr = {(DMA_AW){1'b0}};
		assign	o_dma_data = {(DMA_DW){1'b0}};
		assign	o_dma_sel  = {(DMA_DW/8){1'b0}};
		// }}}
		// }}}

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_dma;
		assign	unused_dma = &{ 1'b0,
`ifdef	SDIO_AXI
				M_AXI_AWREADY, M_AXI_WREADY, M_AXI_ARREADY, 
				M_AXI_BVALID, M_AXI_BID, M_AXI_BRESP,
				M_AXI_RVALID, M_AXI_RID, M_AXI_RDATA,
					M_AXI_RLAST, M_AXI_RRESP,
`else
				i_dma_stall, i_dma_ack, i_dma_data, i_dma_err,
`endif
				dma_sd2s, dma_s2sd,
				sd2s_valid, sd2s_last, sd2s_data,
				dma_abort, dma_addr, dma_len, dma_err, dma_busy,
				s2sd_ready,
				s_valid, s_data, m_ready
				};
		// }}}
		// }}}
	end endgenerate
	// }}}

	//
	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// verilator lint_on  UNUSED
	// verilator coverage_on
	// }}}
endmodule

