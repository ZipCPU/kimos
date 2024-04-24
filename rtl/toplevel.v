////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./toplevel.v
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga -I / -d -o . allclocks.txt clkcheck.txt global.txt crossbus.txt icape.txt version.txt pic.txt pwrcount.txt rtccount.txt spio.txt exconsole.txt wbuuart.txt wbuarbiter.txt bkram.txt flash.txt flashcfg.txt sdram.txt mem_sdram_only.txt mem_flash_sdram.txt zipmaster.txt mdio.txt meganet.txt protocols.txt sdio.txt flashscope.txt mem_flash_bkram.txt mem_bkram_only.txt xdc.txt
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
`default_nettype	none


//
// Here we declare our toplevel.v (toplevel) design module.
// All design logic must take place beneath this top level.
//
// The port declarations just copy data from the @TOP.PORTLIST
// key, or equivalently from the @MAIN.PORTLIST key if
// @TOP.PORTLIST is absent.  For those peripherals that don't need
// any top level logic, the @MAIN.PORTLIST should be sufficent,
// so the @TOP.PORTLIST key may be left undefined.
//
// The only exception is that any clocks with CLOCK.TOP tags will
// also appear in this list
//
module	toplevel(i_clk,
		// SDIO SD Card
o_sdcard_clk,
i_sdcard_cd_n,

		io_sdcard_cmd, io_sdcard_dat,
		// SPIO interface
		i_btn, o_led,
		// UART/host to wishbone interface
		i_wbu_uart_rx, o_wbu_uart_tx,
		// Ethernet control (packets) lines
		i_eth0_rx_clk, i_eth0_rx_ctl, i_eth0_rxd,
		o_eth0_tx_clk, o_eth0_tx_ctl, o_eth0_txd,
		// Toplevel ethernet MDIO ports
		o_eth_mdclk, io_eth_mdio,
		// Top level Quad-SPI I/O ports
		o_qspi_cs_n, io_qspi_dat,
		// SDRAM I/O port wires
		ddr3_reset_n, ddr3_cke, ddr3_ck_p, ddr3_ck_n,
		ddr3_cs_n,
		ddr3_ras_n, ddr3_cas_n, ddr3_we_n,
		ddr3_dqs_p, ddr3_dqs_n,
		ddr3_addr, ddr3_ba,
		o_ddr3_vsel,
		ddr3_dq, ddr3_dm, ddr3_odt,
		i_clk200_p, i_clk200_n);
	//
	// Declaring any top level parameters.
	//
	// These declarations just copy data from the @TOP.PARAM key,
	// or from the @MAIN.PARAM key if @TOP.PARAM is absent.  For
	// those peripherals that don't do anything at the top level,
	// the @MAIN.PARAM key should be sufficient, so the @TOP.PARAM
	// key may be left undefined.
	//
`ifndef	VERILATOR
	localparam	ICAPE_LGDIV=3;
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// EXBUS parameters
	// {{{
	// Baudrate :   1000000
	// Clock    : 100000000
	localparam [23:0] BUSUART = 24'h64;	//   1000000 baud
	localparam	DBGBUSBITS = $clog2(BUSUART);
	// }}}
	parameter	[15:0]	UDP_DBGPORT  = 5929;

	localparam	[47:0]	DEF_ETH0_HWMAC  = 48'h8233_4802e1d0;
	localparam	[31:0]	DEF_ETH0_IPADDR = 32'hc0a80f1a;
	////////////////////////////////////////////////////////////////////////
	//
	// Variables/definitions/parameters used by the ZipCPU bus master
	// {{{
	//
	// A 32-bit address indicating where the ZipCPU should start running
	// from
`ifdef	BKROM_ACCESS
	localparam	RESET_ADDRESS = @$(/bkrom.BASE);
`else
`ifdef	FLASH_ACCESS
	localparam	RESET_ADDRESS = 79691776;
`else
	localparam	RESET_ADDRESS = 167772160;
`endif	// FLASH_ACCESS
`endif	// BKROM_ACCESS
	//
	// The number of valid bits on the bus
	localparam	ZIP_ADDRESS_WIDTH = 25; // Zip-CPU address width
	//
	// Number of ZipCPU interrupts
	localparam	ZIP_INTS = 16;
	//
	// ZIP_START_HALTED
	//
	// A boolean, indicating whether or not the ZipCPU be halted on startup?
`ifdef	BKROM_ACCESS
	localparam	ZIP_START_HALTED=1'b0;
`else
	localparam	ZIP_START_HALTED=1'b1;
`endif
	// }}}
	//
	// Declaring our input and output ports.  We listed these above,
	// now we are declaring them here.
	//
	// These declarations just copy data from the @TOP.IODECLS key,
	// or from the @MAIN.IODECL key if @TOP.IODECL is absent.  For
	// those peripherals that don't do anything at the top level,
	// the @MAIN.IODECL key should be sufficient, so the @TOP.IODECL
	// key may be left undefined.
	//
	// We start with any @CLOCK.TOP keys
	//
	input	wire		i_clk;
	// SDIO SD Card
	// {{{
	output	wire		o_sdcard_clk;


	input	wire		i_sdcard_cd_n;

	inout	wire		io_sdcard_cmd;
	inout	wire	[4-1:0]	io_sdcard_dat;
	// }}}
	// SPIO interface
	input	wire	[2-1:0]	i_btn;
	output	wire	[8-1:0]	o_led;
	input	wire		i_wbu_uart_rx;
	output	wire		o_wbu_uart_tx;
	// MegaNet I/O port declarations
	// {{{
	// output	wire		o_eth0_reset_n;
	input	wire		i_eth0_rx_clk, i_eth0_rx_ctl;
	input	wire [3:0]	i_eth0_rxd;
	output	wire	 	o_eth0_tx_clk, o_eth0_tx_ctl;
	output	wire [3:0]	o_eth0_txd;
	// }}}
	// Ethernet control (MDIO)
	output	wire		o_eth_mdclk;
	inout	wire		io_eth_mdio;
	// Quad SPI flash
	output	wire		o_qspi_cs_n;
	inout	wire	[3:0]	io_qspi_dat;
	// I/O declarations for the DDR3 SDRAM
	// {{{
	output	wire		ddr3_reset_n;
	output	wire	[0:0]	ddr3_cke;
	output	wire		ddr3_ck_p, ddr3_ck_n;
	output	wire	[0:0]	ddr3_cs_n;
	output	wire		ddr3_ras_n, ddr3_cas_n, ddr3_we_n;
	output	wire	[2:0]	ddr3_ba;
	output	wire	[15-1:0]	ddr3_addr;
	// set o_ddr3_vsel = 1'bz for 1.5V SDRAM, = 1'b0 for 1.35V SDRAM
	output	wire		o_ddr3_vsel;
	output	wire	[0:0]			ddr3_odt;
	output	wire	[64/8-1:0]	ddr3_dm;
	inout	wire	[64/8-1:0]	ddr3_dqs_p, ddr3_dqs_n;
	inout	wire	[64-1:0]	ddr3_dq;
	// }}}
	input	wire	i_clk200_p, i_clk200_n;


	//
	// Declaring component data, internal wires and registers
	//
	// These declarations just copy data from the @TOP.DEFNS key
	// within the component data files.
	//
	// SDIO SD Card definitions
	// {{{
	wire		w_sdio_cfg_ddr;
	wire		w_sdio_cfg_ds, w_sdio_cfg_dscmd;
	wire	[4:0]	w_sdio_cfg_sample_shift;
	wire		w_sdio_pp_cmd;
	wire		w_sdio_pp_data;
		//
	wire	[7:0]	w_sdio_sdclk;
	wire		w_sdio_cmd_en;
	wire	[1:0]	w_sdio_cmd_data;
	wire		w_sdio_data_en;
	wire		w_sdio_rx_en;
	wire	[31:0]	w_sdio_tx_data;
		//
	wire	[1:0]	w_sdio_cmd_strb;
	wire	[1:0]	w_sdio_cmd_idata;
	wire		w_sdio_cmd_collision;
	wire		w_sdio_card_busy;
	wire	[1:0]	w_sdio_rx_strb;
	wire	[15:0]	w_sdio_rx_data;
		//
	wire		w_sdio_ac_valid;
	wire	[1:0]	w_sdio_ac_data;
	wire		w_sdio_ad_valid;
	wire	[31:0]	w_sdio_ad_data;

	wire		w_sdio_ck;
	wire		w_sdio_ds;
	wire	[31:0]	w_sdio_debug;
	// }}}

	wire	[8-1:0]	w_led;
	wire	[2-1:0]	w_btn;
	// Mega Net definitions
	// {{{
	wire	[7:0]		w_eth0_rxd, w_eth0_txd;
	wire			w_eth0_rxdv, w_eth0_rxerr,
				w_eth0_txctl;
	wire	[1:0]		w_eth0_tx_clk;
	reg	eth0_last_tck;
	// }}}
	// Ethernet control (MDIO)
	wire		w_mdio, w_mdwe;
	wire		w_qspi_sck, w_qspi_cs_n;
	wire	[1:0]	qspi_bmod;
	wire	[3:0]	qspi_dat;
	// Wires necessary to run the SDRAM
	// {{{
	wire	sdram_cyc, sdram_stb, sdram_we,
		sdram_stall, sdram_ack, sdram_err;
	wire	[(30-6-1):0]	sdram_addr;
	wire	[(512-1):0]	sdram_wdata,
					sdram_rdata;
	wire	[(512/8-1):0]	sdram_sel;

	// }}}
	// Wires coming back from the SDRAM
	wire	s_clk, s_reset;
	// Clock/reset definitions
	// {{{
	wire	i_clk200, i_clk200_buffered;
	wire	s_clk_200mhz,  s_clk_200mhz_unbuffered,
		sysclk_locked, sysclk_feedback, sysclk_feedback_buffered,
		s_clk_125mhz,  s_clk_125_unbuffered,
		// s_clk_150mhz	-- needed for SATA
		s_clk_250mhz,  s_clk_250_unbuffered,
		s_clksync,     s_clksync_unbuffered,
		s_clk_400mhz,  s_clk_400mhz_unbuffered,	// Pixclk * 10
		s_clk_40mhz_unbuffered,	// 40MHz
		netclk_locked, netclk_feedback, netclk_feedback_buffered;
	wire	i_clk_buffered;
	wire	clocks_locked;
	reg	[4:0]	pll_reset_sreg;
	reg		pll_reset;
	// }}}
	// Verilator lint_off UNUSED
	wire		ign_cpu_stall, ign_cpu_ack;
	wire	[31:0]	ign_cpu_idata;
	// Verilator lint_on  UNUSED


	//
	// Time to call the main module within main.v.  Remember, the purpose
	// of the main.v module is to contain all of our portable logic.
	// Things that are Xilinx (or even Altera) specific, or for that
	// matter anything that requires something other than on-off logic,
	// such as the high impedence states required by many wires, is
	// kept in this (toplevel.v) module.  Everything else goes in
	// main.v.
	//
	// We automatically place s_clk, and s_reset here.  You may need
	// to define those above.  (You did, didn't you?)  Other
	// component descriptions come from the keys @TOP.MAIN (if it
	// exists), or @MAIN.PORTLIST if it does not.
	//

	main	thedesign(s_clk, s_reset,
		// SDIO SD Card
		!i_sdcard_cd_n,
		//
		w_sdio_cfg_ddr,
		w_sdio_cfg_ds,
		w_sdio_cfg_dscmd,
		w_sdio_cfg_sample_shift,
		w_sdio_pp_cmd,
		w_sdio_pp_data,
		//
		w_sdio_sdclk,
		w_sdio_cmd_en,
		w_sdio_cmd_data,
		w_sdio_data_en,
		w_sdio_rx_en,
		w_sdio_tx_data,
		//
		w_sdio_cmd_strb,
		w_sdio_cmd_idata,
		w_sdio_cmd_collision,
		w_sdio_card_busy,
		w_sdio_rx_strb,
		w_sdio_rx_data,
		//
		w_sdio_ac_valid,
		w_sdio_ac_data,
		w_sdio_ad_valid,
		w_sdio_ad_data,
		w_sdio_debug,
		w_btn, w_led,
		// UART/host to wishbone interface
		i_wbu_uart_rx, o_wbu_uart_tx,
		// Ethernet (RGMII) connections
		// o_eth0_reset_n,
		i_eth0_rx_clk, w_eth0_rxdv,  w_eth0_rxdv ^ w_eth0_rxerr, w_eth0_rxd,
		w_eth0_tx_clk, w_eth0_txctl, w_eth0_txd,
		o_eth_mdclk, w_mdio, w_mdwe, io_eth_mdio,
		// Quad SPI flash
		w_qspi_cs_n, w_qspi_sck, qspi_dat, io_qspi_dat, qspi_bmod,
		// The SDRAM interface to an toplevel AXI4 module
		//
		sdram_cyc, sdram_stb, sdram_we,
			sdram_addr, sdram_wdata, sdram_sel,
			sdram_stall, sdram_ack, sdram_rdata,
			sdram_err,
		// PLL generated clocks
		s_clk_200mhz, s_clk_125mhz,
		// Simulation bus control for the CPU
		1'b0, 1'b0, 1'b0, 7'h0, 32'h0,
		ign_cpu_stall, ign_cpu_ack, ign_cpu_idata,
		// Reset wire for the ZipCPU
		s_reset);


	//
	// Our final section to the toplevel is used to provide all of
	// that special logic that couldnt fit in main.  This logic is
	// given by the @TOP.INSERT tag in our data files.
	//


	sdfrontend #(
		.OPT_SERDES(1'b0),
		.OPT_DDR(1'b1),
		.NUMIO(4)
	) u_sdio_frontend (
		// {{{
		.i_clk(s_clk), .i_hsclk(s_clk_400mhz), .i_reset(s_reset),
		// Configuration
		.i_cfg_ddr(w_sdio_cfg_ddr),
		.i_cfg_ds(w_sdio_cfg_ds),
		.i_cfg_dscmd(w_sdio_cfg_dscmd),
		.i_sample_shift(w_sdio_cfg_sample_shift),
		.i_pp_cmd(w_sdio_pp_cmd),
		.i_pp_data(w_sdio_pp_data),
		// Run-time inputs
		.i_sdclk(w_sdio_sdclk),
		.i_cmd_en(w_sdio_cmd_en),
		.i_cmd_data(w_sdio_cmd_data),
		.i_data_en(w_sdio_data_en),
		.i_rx_en(w_sdio_rx_en),
		.i_tx_data(w_sdio_tx_data),
		// Return values
		.o_cmd_strb(w_sdio_cmd_strb),
		.o_cmd_data(w_sdio_cmd_idata),
		.o_cmd_collision(w_sdio_cmd_collision),
		.o_data_busy(w_sdio_card_busy),
		.o_rx_strb( w_sdio_rx_strb),
		.o_rx_data( w_sdio_rx_data),
		//
		.MAC_VALID(w_sdio_ac_valid),
		.MAC_DATA( w_sdio_ac_data),
		.MAD_VALID(w_sdio_ad_valid),
		.MAD_DATA( w_sdio_ad_data),
		// IO ports
		.o_ck(w_sdio_ck),
		.i_ds(w_sdio_ds),
		.io_cmd(io_sdcard_cmd),
		.io_dat(io_sdcard_dat),
		.o_debug(w_sdio_debug)
		// }}}
	);


	assign	o_sdcard_clk = w_sdio_ck;

	assign	w_sdio_ds    = 1'b0;


	// LEDs 5:0 are inverted.  For these LEDs, a '1' is off, and a '0' is on
	assign	o_led = { (w_led[7] || s_reset),	// Baseboard inner LED
			(w_led[6] || !clocks_locked),	// Baseboard LED
			w_led[5:4],		// Last two baseboard LEDs
			w_led[3:0] };		// Daughter board LEDs

	assign	w_btn = { ~i_btn };

	// RGMII control
	// {{{
	xiddr	eth0rx0(i_eth0_rx_clk, i_eth0_rxd[0], { w_eth0_rxd[4], w_eth0_rxd[0] });
	xiddr	eth0rx1(i_eth0_rx_clk, i_eth0_rxd[1], { w_eth0_rxd[5], w_eth0_rxd[1] });
	xiddr	eth0rx2(i_eth0_rx_clk, i_eth0_rxd[2], { w_eth0_rxd[6], w_eth0_rxd[2] });
	xiddr	eth0rx3(i_eth0_rx_clk, i_eth0_rxd[3], { w_eth0_rxd[7], w_eth0_rxd[3] });
	xiddr	eth0rxc(i_eth0_rx_clk, i_eth0_rx_ctl, { w_eth0_rxdv,   w_eth0_rxerr });

	//
	// All of the below is about delaying the clock 90 degrees from the data
	//
	xoserdes	eth0tx0(s_clk_125mhz, pll_reset, s_clk_250mhz, { {(2){w_eth0_txd[0]}}, {(2){w_eth0_txd[4]}} }, o_eth0_txd[0]);
	xoserdes	eth0tx1(s_clk_125mhz, pll_reset, s_clk_250mhz, { {(2){w_eth0_txd[1]}}, {(2){w_eth0_txd[5]}} }, o_eth0_txd[1]);
	xoserdes	eth0tx2(s_clk_125mhz, pll_reset, s_clk_250mhz, { {(2){w_eth0_txd[2]}}, {(2){w_eth0_txd[6]}} }, o_eth0_txd[2]);
	xoserdes	eth0tx3(s_clk_125mhz, pll_reset, s_clk_250mhz, { {(2){w_eth0_txd[3]}}, {(2){w_eth0_txd[7]}} }, o_eth0_txd[3]);

	always @(posedge s_clk_125mhz)
		eth0_last_tck <= w_eth0_tx_clk[0];

	xoserdes	eth0txc(s_clk_125mhz, pll_reset, s_clk_250mhz, {(4){w_eth0_txctl}}, o_eth0_tx_ctl );

	xoserdes	eth0txck(s_clk_125mhz, pll_reset, s_clk_250mhz, {eth0_last_tck, {(2){w_eth0_tx_clk[1]}},w_eth0_tx_clk[0]},o_eth0_tx_clk);
	// xoserdes	eth0txck(s_clk_125mhz, pll_reset, s_clk_250mhz, { {(2){w_eth0_tx_clk[1]}},{(2){w_eth0_tx_clk[0]}} }, o_eth0_tx_clk);
	// }}}

	assign	io_eth_mdio = (w_mdwe)?w_mdio : 1'bz;

	//
	//
	// Wires for setting up the QSPI flash wishbone peripheral
	//
	//
	// QSPI)BMOD, Quad SPI bus mode, Bus modes are:
	//	0?	Normal serial mode, one bit in one bit out
	//	10	Quad SPI mode, going out
	//	11	Quad SPI mode coming from the device (read mode)
	assign io_qspi_dat = (~qspi_bmod[1])?({2'b11,1'bz,qspi_dat[0]})
				:((qspi_bmod[0])?(4'bzzzz):(qspi_dat[3:0]));
	assign	o_qspi_cs_n = w_qspi_cs_n;

	// The following primitive is necessary in many designs order to gain
	// access to the o_qspi_sck pin.  It's not necessary on the Arty,
	// simply because they provide two pins that can drive the QSPI
	// clock pin.
	wire	[3:0]	su_nc;	// Startup primitive, no connect
	STARTUPE2 #(
		// {{{
		// Leave PROG_USR false to avoid activating the program
		// event security feature.  Notes state that such a feature
		// requires encrypted bitstreams.
		.PROG_USR("FALSE"),
		// Sets the configuration clock frequency (in ns) for
		// simulation.
		.SIM_CCLK_FREQ(0.0)
		// }}}
	) STARTUPE2_inst (
		// {{{
		// CFGCLK, 1'b output: Configuration main clock output -- no
		//	connect
		.CFGCLK(su_nc[0]),
		// CFGMCLK, 1'b output: Configuration internal oscillator clock
		//	output
		.CFGMCLK(su_nc[1]),
		// EOS, 1'b output: Active high output indicating the End Of
		//	Startup.
		.EOS(su_nc[2]),
		// PREQ, 1'b output: PROGRAM request to fabric output
		//	Only enabled if PROG_USR is set.  This lets the fabric
		//	know that a request has been made (either JTAG or pin
		//	pulled low) to program the device
		.PREQ(su_nc[3]),
		// CLK, 1'b input: User start-up clock input
		.CLK(1'b0),
		// GSR, 1'b input: Global Set/Reset input
		.GSR(1'b0),
		// GTS, 1'b input: Global 3-state input
		.GTS(1'b0),
		// KEYCLEARB, 1'b input: Clear AES Decrypter Key input from
		//	BBRAM
		.KEYCLEARB(1'b0),
		// PACK, 1-bit input: PROGRAM acknowledge input
		//	This pin is only enabled if PROG_USR is set.  This
		//	allows the FPGA to acknowledge a request for reprogram
		//	to allow the FPGA to get itself into a reprogrammable
		//	state first.
		.PACK(1'b0),
		// USRCLKO, 1-bit input: User CCLK input -- This is why I am
		//	using this module at all.
		.USRCCLKO(w_qspi_sck),
		// USRCCLKTS, 1'b input: User CCLK 3-state enable input
		//	An active high here places the clock into a high
		//	impedence state.  Since we wish to use the clock as an
		//	active output always, we drive this pin low.
		.USRCCLKTS(1'b0),
		// USRDONEO, 1'b input: User DONE pin output control
		//	Set this to "high" to make sure that the DONE LED pin
		//	is high.
		.USRDONEO(1'b1),
		// USRDONETS, 1'b input: User DONE 3-state enable output
		//	This enables the FPGA DONE pin to be active.  Setting
		//	this active high sets the DONE pin to high impedence,
		//	setting it low allows the output of this pin to be as
		//	stated above.
		.USRDONETS(1'b1)
		// }}}
	);


	wire	[31:0]	sdram_debug;

	// Force VSEL to 1'bz, to make the DDR3 SDRAM operate at 1.5V.
	assign	o_ddr3_vsel = 1'bz;

	migsdram #(
		// {{{
		.AXIDWIDTH(1), .WBDATAWIDTH(512),
		.DDRWIDTH(64),
		.DDRAWID(15),
		.RAMABITS(30)
		// }}}
	) sdrami(
		// {{{
		.i_clk(i_clk200_buffered),
		.i_clk_200mhz(s_clk_200mhz),
		.o_sys_clk(s_clk),
		// .i_reset(!i_cpu_resetn),
		// pll_reset is an asynchronous incoming reset.  It does not
		// require any synchronization, as the MIG synchronizes it
		// internally
		.i_reset(pll_reset),
		.o_sys_reset(s_reset),
		//
		.i_wb_cyc(sdram_cyc), .i_wb_stb(sdram_stb),
		.i_wb_we(sdram_we), .i_wb_addr(sdram_addr),
			.i_wb_data(sdram_wdata), .i_wb_sel(sdram_sel),
		.o_wb_stall(sdram_stall),    .o_wb_ack(sdram_ack),
			.o_wb_data(sdram_rdata), .o_wb_err(sdram_err),
		//
		.o_ddr_ck_p(ddr3_ck_p), .o_ddr_ck_n(ddr3_ck_n),
		.o_ddr_reset_n(ddr3_reset_n), .o_ddr_cke(ddr3_cke),
		.o_ddr_cs_n(ddr3_cs_n),
		.o_ddr_ras_n(ddr3_ras_n),
		.o_ddr_cas_n(ddr3_cas_n), .o_ddr_we_n(ddr3_we_n),
		.o_ddr_ba(ddr3_ba), .o_ddr_addr(ddr3_addr),
		.o_ddr_odt(ddr3_odt), .o_ddr_dm(ddr3_dm),
		.io_ddr_dqs_p(ddr3_dqs_p), .io_ddr_dqs_n(ddr3_dqs_n),
		.io_ddr_data(ddr3_dq)
		// }}}
	);
 	

	// Buffer the incoming clock
	BUFG masterclkclkbufi(.I(i_clk), .O(i_clk_buffered));
	IBUFDS masterclkio2clk (.I(i_clk200_p), .IB(i_clk200_n), .O(i_clk200));
	BUFG masterclkclk2bufi(.I(i_clk200), .O(i_clk200_buffered));

	// pll_reset
	initial	{ pll_reset, pll_reset_sreg } = -1;
	always @(posedge i_clk_buffered)
		{ pll_reset, pll_reset_sreg } <= { pll_reset_sreg, 1'b0 };

	////////////////////////////////////////////////////////////////////////
	//
	// PLL #1: 100MHz, 200MHz, 400MHz, and 40MHz
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// But ... the delay controller requires a 200 MHz reference clock,
	// the generic clock generator requires a 400MHz clock and a clock
	// synchronized to it
	PLLE2_BASE #(
		// {{{
		.CLKFBOUT_MULT(4),	// Multiply up to 800MHz
		.CLKFBOUT_PHASE(0.0),
		.CLKIN1_PERIOD(5),
		.CLKOUT0_DIVIDE(4),	// 200 MHz
		.CLKOUT1_DIVIDE(2),	// 400 MHz
		.CLKOUT2_DIVIDE(8),	// 100 MHz
		.CLKOUT3_DIVIDE(20)	//  40 MHz
		// }}}
	) gen_sysclk(
		// {{{
		.CLKIN1(i_clk200_buffered),
		.CLKOUT0(s_clk_200mhz_unbuffered),
		.CLKOUT1(s_clk_400mhz_unbuffered),
		.CLKOUT2(s_clksync_unbuffered),
		.CLKOUT3(s_clk_40mhz_unbuffered),
		.PWRDWN(1'b0), .RST(pll_reset),
		.CLKFBOUT(sysclk_feedback),
		.CLKFBIN(sysclk_feedback_buffered),
		.LOCKED(sysclk_locked)
		// }}}
	);

	BUFG	sysbuf(     .I(s_clk_200mhz_unbuffered),.O(s_clk_200mhz));
	// BUFG	clksync_buf(.I(s_clksync_unbuffered),   .O(s_clksync));
	BUFG	clk4x_buf(  .I(s_clk_400mhz_unbuffered),.O(s_clk_400mhz));
	BUFG	sys_feedback(.I(sysclk_feedback),.O(sysclk_feedback_buffered));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PLL #2: 125MHz, 250MHz
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The ethernet MAC requires a 125MHz clock
	//   We can't trust the RX 125MHz clock for this, since there's a
	//   possibility the RX 125MHz clock might arrive at a different rate.
	//   
	PLLE2_BASE #(
		// {{{
		.CLKFBOUT_MULT(5),
		.CLKFBOUT_PHASE(0.0),
		.CLKIN1_PERIOD(5),
		.CLKOUT0_DIVIDE(8),	// 125 MHz
		.CLKOUT0_PHASE(0),
		.CLKOUT1_DIVIDE(4),	// 250 MHz
		.CLKOUT1_PHASE(0)
		// }}}
	) gen_netclk(
		// {{{
		.CLKIN1(i_clk200_buffered),
		.CLKOUT0(s_clk_125_unbuffered),
		.CLKOUT1(s_clk_250_unbuffered),
		.PWRDWN(1'b0), .RST(pll_reset),
		.CLKFBOUT(netclk_feedback),
		.CLKFBIN(netclk_feedback_buffered),
		.LOCKED(netclk_locked)
		// }}}
	);

	BUFG	netbuf(.I(s_clk_125_unbuffered), .O(s_clk_125mhz));
	BUFG	netbf5(.I(s_clk_250_unbuffered), .O(s_clk_250mhz));
	BUFG	netfb(.I(netclk_feedback), .O(netclk_feedback_buffered));

	assign	clocks_locked = (netclk_locked && sysclk_locked);

	// }}}



endmodule // end of toplevel.v module definition
