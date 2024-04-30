////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/migsdram.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	To interface a Xilinx board to a MIG Generated SDRAM
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
`default_nettype	none
// }}}
module	migsdram #(
		// {{{
		parameter	DDRWIDTH = 16, WBDATAWIDTH=(DDRWIDTH*8),
		parameter	AXIDWIDTH = 1,
		// The SDRAM address bits (RAMABITS) are a touch more difficult
		// to work out.  Here we leave them as a fixed parameter, but
		// there are consequences to this.  Specifically, the wishbone
		// data width, the wishbone address width, and this number have
		// interactions not well captured here.
		parameter	RAMABITS = 28,
		// DDRAWID: The number of physical address wires to the DDR3
		// memory.
		parameter	DDRAWID = 14,
		// All DDR3 memories have 8 timeslots.  Thus, if the DDR3 memory
		// has DDRWIDTH bits to it, the entire transaction must take
		// AXIWIDTH = 8 times that many bits ...
		localparam	AXIWIDTH= DDRWIDTH *8,
		localparam	DW=WBDATAWIDTH,
		localparam	AW=RAMABITS-$clog2(WBDATAWIDTH/8),
		localparam	SELW= (WBDATAWIDTH/8),
		// ACTIVE_LOW_MIG_RESET is based upon how the MIG is configured.
		// If it's configured to produce an active low reset, then we'll
		// need to swap polarity here before we can use it to generate
		// an active high reset output.
		localparam [0:0]	ACTIVE_LOW_MIG_RESET = 1'b1
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_clk_200mhz,
		output	wire			o_sys_clk,
		input	wire			i_reset,
		output	wire			o_sys_reset,
		// Wishbone bus slave port
		// {{{
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[(AW-1):0]	i_wb_addr,
		input	wire	[(DW-1):0]	i_wb_data,
		input	wire	[(SELW-1):0]	i_wb_sel,
		output	wire			o_wb_stall, o_wb_ack,
		output	wire	[(DW-1):0]	o_wb_data,
		output	wire			o_wb_err,
		// }}}
		// SDRAM connections
		// {{{
		output	wire	[0:0]			o_ddr_ck_p, o_ddr_ck_n,
		output	wire				o_ddr_reset_n,
		output	wire	[0:0]			o_ddr_cke,
		output	wire	[0:0]			o_ddr_cs_n,
		output	wire				o_ddr_ras_n,o_ddr_cas_n,
							o_ddr_we_n,
		output	wire	[2:0]			o_ddr_ba,
		output	wire	[DDRAWID-1:0]		o_ddr_addr,
		output	wire	[0:0]			o_ddr_odt,
		output	wire	[(DDRWIDTH/8-1):0]	o_ddr_dm,
		inout	wire	[(DDRWIDTH/8)-1:0]	io_ddr_dqs_p,
							io_ddr_dqs_n,
		inout	wire	[(DDRWIDTH-1):0]	io_ddr_data
		// }}}
		// Debug connection (unused)
		// output	wire	[31:0]			o_ram_dbg
		// }}}
	);

`define	SDRAM_ACCESS
`ifdef	SDRAM_ACCESS
	// Local declarations
	// {{{
	// Write address channel
	wire	[(AXIDWIDTH-1):0]	s_axi_awid;
	wire	[(RAMABITS-1):0]	s_axi_awaddr;
	wire	[7:0]			s_axi_awlen;
	wire	[2:0]			s_axi_awsize;
	wire	[1:0]			s_axi_awburst;
	wire	[0:0]			s_axi_awlock;
	wire	[3:0]			s_axi_awcache;
	wire	[2:0]			s_axi_awprot;
	wire	[3:0]			s_axi_awqos;
	wire				s_axi_awvalid;
	wire				s_axi_awready;
	// Writei data channel
	wire	[(AXIWIDTH-1):0]	s_axi_wdata;
	wire	[(AXIWIDTH/8-1):0]	s_axi_wstrb;
	wire				s_axi_wlast, s_axi_wvalid, s_axi_wready;
	// Write response channel
	wire				s_axi_bready;
	wire	[(AXIDWIDTH-1):0]	s_axi_bid;
	wire	[1:0]			s_axi_bresp;
	wire				s_axi_bvalid;

	// Read address channel
	wire	[(AXIDWIDTH-1):0]	s_axi_arid;
	wire	[(RAMABITS-1):0]	s_axi_araddr;
	wire	[7:0]			s_axi_arlen;
	wire	[2:0]			s_axi_arsize;
	wire	[1:0]			s_axi_arburst;
	wire	[0:0]			s_axi_arlock;
	wire	[3:0]			s_axi_arcache;
	wire	[2:0]			s_axi_arprot;
	wire	[3:0]			s_axi_arqos;
	wire				s_axi_arvalid;
	wire				s_axi_arready;
	// Read response/data channel
	wire	[(AXIDWIDTH-1):0]	s_axi_rid;
	wire	[(AXIWIDTH-1):0]	s_axi_rdata;
	wire	[1:0]			s_axi_rresp;
	wire				s_axi_rlast;
	wire				s_axi_rvalid;
	wire				s_axi_rready;

	// Other wires ...
	wire		init_calib_complete, mmcm_locked;
	wire		app_sr_active, app_ref_ack, app_zq_ack;
	wire		app_sr_req, app_ref_req, app_zq_req;
	wire		w_sys_reset;
	// wire	[11:0]	w_device_temp;
	// }}}

	mig_axis
	mig_sdram(
		// {{{
		.ddr3_ck_p(o_ddr_ck_p),		.ddr3_ck_n(o_ddr_ck_n),
		.ddr3_reset_n(o_ddr_reset_n),	.ddr3_cke(o_ddr_cke),
		.ddr3_cs_n(o_ddr_cs_n),
		.ddr3_ras_n(o_ddr_ras_n),
		.ddr3_we_n(o_ddr_we_n),		.ddr3_cas_n(o_ddr_cas_n),
		.ddr3_ba(o_ddr_ba),		.ddr3_addr(o_ddr_addr),
		.ddr3_odt(o_ddr_odt),
		.ddr3_dqs_p(io_ddr_dqs_p),	.ddr3_dqs_n(io_ddr_dqs_n),
		.ddr3_dq(io_ddr_data),		.ddr3_dm(o_ddr_dm),
		//
		.sys_clk_i(i_clk),
		.clk_ref_i(i_clk_200mhz),
		.ui_clk(o_sys_clk),
		.ui_clk_sync_rst(w_sys_reset),
		.mmcm_locked(mmcm_locked),
		// aresetn is an AXI signal.  This could be i_reset, but i_reset
		// isn't in the UI clock domain.
		.aresetn(1'b1),
		.app_sr_req(1'b0),
		.app_ref_req(1'b0),
		.app_zq_req(1'b0),
		.app_sr_active(app_sr_active),
		.app_ref_ack(app_ref_ack),
		.app_zq_ack(app_zq_ack),
		//
		.s_axi_awid(s_axi_awid),	.s_axi_awaddr(s_axi_awaddr),
		.s_axi_awlen(s_axi_awlen),	.s_axi_awsize(s_axi_awsize),
		.s_axi_awburst(s_axi_awburst),	.s_axi_awlock(s_axi_awlock),
		.s_axi_awcache(s_axi_awcache),	.s_axi_awprot(s_axi_awprot),
		.s_axi_awqos(s_axi_awqos),	.s_axi_awvalid(s_axi_awvalid),
		.s_axi_awready(s_axi_awready),
		//
		.s_axi_wready(	s_axi_wready),
		.s_axi_wdata(	s_axi_wdata),
		.s_axi_wstrb(	s_axi_wstrb),
		.s_axi_wlast(	s_axi_wlast),
		.s_axi_wvalid(	s_axi_wvalid),
		//
		.s_axi_bready(s_axi_bready),	.s_axi_bid(s_axi_bid),
		.s_axi_bresp(s_axi_bresp),	.s_axi_bvalid(s_axi_bvalid),
		//
		.s_axi_arid(s_axi_arid),	.s_axi_araddr(s_axi_araddr),
		.s_axi_arlen(s_axi_arlen),	.s_axi_arsize(s_axi_arsize),
		.s_axi_arburst(s_axi_arburst),	.s_axi_arlock(s_axi_arlock),
		.s_axi_arcache(s_axi_arcache),	.s_axi_arprot(s_axi_arprot),
		.s_axi_arqos(s_axi_arqos),	.s_axi_arvalid(s_axi_arvalid),
		.s_axi_arready(s_axi_arready),
		//
		.s_axi_rready(s_axi_rready),	.s_axi_rid(s_axi_rid),
		.s_axi_rdata(s_axi_rdata),	.s_axi_rresp(s_axi_rresp),
		.s_axi_rlast(s_axi_rlast),	.s_axi_rvalid(s_axi_rvalid),
		.init_calib_complete(init_calib_complete),
		.sys_rst(i_reset ^ ACTIVE_LOW_MIG_RESET)
		// , .device_temp_i(12'h0), .device_temp(w_device_temp)
		// }}}
	);

	wbm2axisp #(
		// {{{
		.C_AXI_ID_WIDTH(AXIDWIDTH),
		.C_AXI_DATA_WIDTH(AXIWIDTH),
		.C_AXI_ADDR_WIDTH(RAMABITS),
		.AW(AW), .DW(DW)
		// }}}
	) bus_translator (
		// {{{
			.i_clk(o_sys_clk),
			.i_reset(o_sys_reset), // internally unused
			// Write address channel signals
			.o_axi_awid(	s_axi_awid),
			.o_axi_awaddr(	s_axi_awaddr),
			.o_axi_awlen(	s_axi_awlen),
			.o_axi_awsize(	s_axi_awsize),
			.o_axi_awburst(	s_axi_awburst),
			.o_axi_awlock(	s_axi_awlock),
			.o_axi_awcache(	s_axi_awcache),
			.o_axi_awprot(	s_axi_awprot),  // s_axi_awqos
			.o_axi_awqos(	s_axi_awqos),  // s_axi_awqos
			.o_axi_awvalid(	s_axi_awvalid),
			.i_axi_awready(	s_axi_awready),
		//
			.i_axi_wready(	s_axi_wready),
			.o_axi_wdata(	s_axi_wdata),
			.o_axi_wstrb(	s_axi_wstrb),
			.o_axi_wlast(	s_axi_wlast),
			.o_axi_wvalid(	s_axi_wvalid),
		//
			.o_axi_bready(	s_axi_bready),
			.i_axi_bid(	s_axi_bid),
			.i_axi_bresp(	s_axi_bresp),
			.i_axi_bvalid(	s_axi_bvalid),
		//
			.i_axi_arready(	s_axi_arready),
			.o_axi_arid(	s_axi_arid),
			.o_axi_araddr(	s_axi_araddr),
			.o_axi_arlen(	s_axi_arlen),
			.o_axi_arsize(	s_axi_arsize),
			.o_axi_arburst(	s_axi_arburst),
			.o_axi_arlock(	s_axi_arlock),
			.o_axi_arcache(	s_axi_arcache),
			.o_axi_arprot(	s_axi_arprot),
			.o_axi_arqos(	s_axi_arqos),
			.o_axi_arvalid(	s_axi_arvalid),
		//
			.o_axi_rready(	s_axi_rready),
			.i_axi_rid(	s_axi_rid),
			.i_axi_rdata(	s_axi_rdata),
			.i_axi_rresp(	s_axi_rresp),
			.i_axi_rlast(	s_axi_rlast),
			.i_axi_rvalid(	s_axi_rvalid),
		//
			.i_wb_cyc(	i_wb_cyc),
			.i_wb_stb(	i_wb_stb),
			.i_wb_we(	i_wb_we),
			.i_wb_addr(	i_wb_addr),
			.i_wb_data(	i_wb_data),
			.i_wb_sel(	i_wb_sel),
		//
			.o_wb_stall(	o_wb_stall),
			.o_wb_ack(	o_wb_ack),
			.o_wb_data(	o_wb_data),
			.o_wb_err(	o_wb_err)
		//
			// , .o_dbg(	o_ram_dbg)
		// }}}
	);

	// assign	o_ram_dbg = 32'h0;

	// Convert from active low to active high, *and* hold the system in
	// reset until the memory comes up.

	// o_sys_reset
	// {{{
	reg	r_sys_reset;
	initial	r_sys_reset = 1'b1;
	always @(posedge o_sys_clk)
		r_sys_reset <= (w_sys_reset ^ ACTIVE_LOW_MIG_RESET)
				||(!init_calib_complete)
				||(!mmcm_locked);

	BUFG resetbuf(.I(r_sys_reset), .O(o_sys_reset));
	// }}}
`else
	// If not defined SDRAM_ACCESS
	// {{{
	BUFG	sysclk(i_clk, o_sys_clk);
	initial	o_sys_reset <= 1'b1;
	always	@(posedge i_clk)
		o_sys_reset <= 1'b1;

	OBUFDS ckobuf(.I(i_clk), .O(o_ddr_ck_p), .OB(o_ddr_ck_n));

	assign	o_ddr_reset_n	= 1'b0;
	assign	o_ddr_cke[0]	= 1'b0;
	assign	o_ddr_cs_n[0]	= 1'b1;
	assign	o_ddr_cas_n	= 1'b1;
	assign	o_ddr_ras_n	= 1'b1;
	assign	o_ddr_we_n	= 1'b1;
	assign	o_ddr_ba	= 3'h0;
	assign	o_ddr_addr	= {(DDRAWID){1'b0}};
	assign	o_ddr_dm	= 2'b00;
	assign	io_ddr_data	= 16'h0;

	OBUFDS	dqsbufa(.I(i_clk), .O(io_ddr_dqs_p[1]), .OB(io_ddr_dqs_n[1]));
	OBUFDS	dqsbufb(.I(i_clk), .O(io_ddr_dqs_p[0]), .OB(io_ddr_dqs_n[0]));
	// }}}
`endif
endmodule


