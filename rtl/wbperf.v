////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbperf
// {{{
// Project:	WB2AXIPSP: bus bridges and other odds and ends
//
// Purpose:	Measure the performance of a high speed Wishbone interface.  The
// {{{
//		following monitor requires connecting to both an Wishbone
//	control slave interface, as well as a second Wishbone interface as a
//	monitor.  But must be Wishbone pipelined--not classic.  The Wishbone
//	monitor interface is read only, and (ideally) shouldn't be corrupted by
//	the inclusion of the control interface on the same bus.
//
//	The core works by counting clock cycles in a fashion that should
//	supposedly make it easy to calculate 1) throughput, and 2) lag.
//	Moreover, the counters are arranged such that after the fact, the
//	various contributors to throughput can be measured and evaluted: was
//	the slave the holdup?  Or was it the master?
//
//	To use the core, connect it and build your design.  Then write a '3'
//	to register 15 (address 60).  Once the bus returns to idle, the core
//	will begin capturing data and statistics.  When done, write a '0' to
//	the same register.  This will create a stop request.  Once the bus
//	comes to a stop, the core will stop accumulating values into its
//	statistics.  Those statistics can then be read out from the AXI-lite
//	bus and analyzed.
// }}}
// Goals:
// {{{
//	My two biggest goals are to measure throughput and lag.  Defining those
//	two measures, of course, is half the battle.   The other half of the
//	battle is knowing which side to blame for any particular issue.
//
//	Let's start with the total time required for any transaction.  This
//	equals the time from the indication of a request to the last response.
//	We'll use a linear model to describe this transaction time:
//
//	Transaction time = Latency + (Beats in transaction) / Throughput
//
//	The goal of this core is to help you identify latency and throughput
//	numbers.
//
//	One measure might be to take the total number of clock cycles, from when
//	the core was enabled to when it was disabled, and to divide by the
//	number of beats transmitted.
//
//	(Poor) Throughput = (Total beats transferred) / (total time)
//
//	In a heavily used bus, this might be a good enough measure.  However,
//	this is a poor measure for most systems where the bus is idle most of
//	the time.  Instead, it might be nice to start the measurement early
//	on during some task, and conclude it much later.  In the meantime, the
//	bus might go from idle to busy and back again many times.  For example,
//	you don't want to copy information from the disk drive if you haven't
//	made a request of the controller.  For these reasons, we try to achieve
//	a better measurement.
//
//	Here's the basic approach: we'll look at all of the clocks associated
//	with any particular type of transaction, and lump them into a couple
//	of categories: latency limiting clocks and throughput limiting clocks.
//	We'll then divide the latency limiting clocks by the number of bursts
//	that have taken place, and divide the total number of beats by the
//	time taken to transmit them.
//
//		Latency = (latency measures) / (bursts)
//		Throughput = (beats) / (transmission duration, inc. beats)
//
//	In general, we'll define the transmission duration as the time from the
//	first clock cycle that STB is raised until the final cycle when STB is
//	lowered.  Any idle cycles during this time are marked as a latency
//	measure, not a throughput measure of transmission duration.
//
//	Latency measures, on the other hand, are anything that appear to be
//	burst related--such as the time from the request to the first
//	RVALID (or WVALID), or similarly the time from the last WVALID && WLAST
//	until the final BVALID && BREADY.
//
//	These measures are listed in more detail below.
//
//	Certain measures below are marked as *ORTHOGONAL*.  These are perhaps
//	better known as (independent), but I started calling them orthogonal
//	and ... will probably do so for some time.  Orthogonal measures are
//	those that don't overlap.  For example, if you just counted AWVALID
//	&& AWREADY (bursts) and WVALID && WREADY clock cycles (beats), you might
//	get a big overlap between the two and so not know which to count.  Not
//	so with the orthogonal measures.
//
//	Further, at the end of every list of orthogonal measures is a metric
//	that can be used to calculate total cycles used--that way you know
//	how the measures relate.
// }}}
// Registers
// {{{
//	  0: Active time
//		Number of clock periods that the performance monitor has been
//		accumulating data for.  This register has a protection measure
//		built into it: if it ever overflows, it will report a
//		32'hffff_ffff value.  This is your indication that other values
//		from within this performance measure are not to be trusted.
//		Either increase LGCNT or try a shorter collection time to fix
//		such a condition.
//
//	  4: CYC cycles -- i.e. the number of clock cycles where CYC is active
//
//	    CYC STB STALL ACK OUT
//	  0: x    x    x    x   x	= Total cycles
//	  -: 0    x    x    x   x	= Total cycles - CYC cycles
//	  4: 1    1    0    x   x	= STB
//	  8: 1    1    1    x   x	= Stall
//	 12: 1    1    1    1   x	= Stall n ACK
//	 16: 1    1    0    1   x	= STB n ACK
//	 20: 1    0    x    1   x	= ACK
//	 24: 1    0    x    0   +	= Wait
//	 28: 1    0    x    0   0	= Tail
//	
//	 32: BUS-ERR: (!CYC && $past(ERR)) # of bus errors (and associated aborts)
//	 36: BUS-ABORT: (!CYC && wb_outstanding > 0 && !$past(ERR)) # of bus errors (and associated aborts)
//	 40: BYTES-REQUESTED: (STB && !STALL ? $countones(SEL) : 0)
//	 44: WRITE-BYTES (STB && !STALL && WE ? $countones(SEL) : 0)
//		 Read Bytes requested (total bytes - write bytes requested)
//	 48: WRITE-BEATS (STB && !STALL && WE) Writes requested
//		Reads requested = beats requested - write beats
//
//	 60(6'hf): Control register
//		Write a 1 to this register to start recording, and a 0 to this
//		register to stop.  Writing a 2 will clear the counters as
//		well.
//
//		This performance monitor depends on certain counters to make
//		sure it can recognize when the bus is idle.  If any of these
//		counters overflow, then the core cannot tell when to start
//		or stop counting and so all performance measures will then be
//		invalid.  If this happens, the perf_error (bit 3) will be set.
//		This bit can only be cleared on a full bus reset--often
//		requiring a power cycle.
//
// Performance:
//	Write Throughput = (Wr Beats) / (Wr Beats + WrStalls + WrSlow);
//	Read Throughput = (Rd Beats) / (Rd Beats + R Stalls + RSlow);
//	Read Latency    = (AR Stalls + RdLag) ./ (Rd Bursts)
// }}}
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2020-2022, Gisselquist Technology, LLC
// {{{
//
// This file is part of the WB2AXIP project.
//
// The WB2AXIP project contains free software and gateware, licensed under the
// Apache License, Version 2.0 (the "License").  You may not use this project,
// or this file, except in compliance with the License.  You may obtain a copy
// of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	wbperf #(
		// {{{
		parameter	DW = 32,
		parameter [0:0]	OPT_LOWPOWER = 0,
		parameter	LGCNT = 32
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[3:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		//
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		//
		//
		// The WB Monitor interface
		//
		input	wire		i_mon_cyc, i_mon_stb, i_mon_we,
		input	wire [DW/8-1:0]	i_mon_sel,
		//
		input	wire		i_mon_stall,
		input	wire		i_mon_ack, i_mon_err
		// }}}
	);

	// Local declarations
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg		triggered, stop_request, clear_request, start_request,
			perf_err, write_en, read_en;
	wire		idle_bus;
	reg	[LGCNT:0]	active_cycles;

	// Measures
	// {{{
	reg	[LGCNT:0]	byte_count;
	reg	[LGCNT-1:0]	total_stb, total_stall, total_stb_ack,
				total_stall_ack, simple_acks, wait_count,
				tail_count, tail_count_aux, bus_errs,
				bus_aborts, write_bytes, write_beats,
				hold_count, num_cyc;
	reg			last_cyc;

	reg	[LGCNT-1:0]	mon_outstanding;
	reg			mon_zero;
	// }}}

	// integer		ik;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// WB control signaling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	o_wb_stall = 1'b0;

	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= i_wb_stb && !o_wb_stall;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// WB register logic
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	begin
		if (idle_bus)
			clear_request <= 1'b0;
		if (!clear_request && idle_bus)
		begin
			start_request <= 0;
			stop_request <= 0;
		end

		if (i_wb_stb && !o_wb_stall && i_wb_we)
		begin
			case(i_wb_addr)
			4'hf:	if (i_wb_sel[0]) begin
				// Start, stop, clear, reset
				//
				clear_request <=  (clear_request && !idle_bus)
					|| (i_wb_data[1] && !i_wb_data[0]);
				stop_request  <= !i_wb_data[0];
				start_request <=  i_wb_data[0] && (!stop_request);

				write_en <= i_wb_data[4] && i_wb_data[0];
				read_en  <= i_wb_data[5] && i_wb_data[0];
				if (i_wb_data[5:4] == 2'b00)
					{ write_en, read_en } <= 2'b11;
				if (!i_wb_data[0])
					{ write_en, read_en } <= 2'b00;
				end
			default: begin end
			endcase
		end

		if (i_reset)
		begin
			clear_request <= 1'b0;
			stop_request  <= 1'b0;
			start_request <= 1'b0;
		end
	end

	always @(posedge i_clk)
	if (OPT_LOWPOWER && (!i_wb_stb || i_wb_we || i_wb_sel == 0))
		o_wb_data <= 0;
	else begin
		o_wb_data <= 0;

		case(i_wb_addr)
		4'h0: begin
			// {{{
			if (!active_cycles[LGCNT])
				o_wb_data[LGCNT-1:0] <= active_cycles[LGCNT-1:0];
			else
				// OVERFLOW!
				o_wb_data <= -1;
			end
			// }}}
		4'h1: o_wb_data[LGCNT-1:0] <= total_stb;
		4'h2: o_wb_data[LGCNT-1:0] <= total_stall;
		4'h3: o_wb_data[LGCNT-1:0] <= total_stall_ack;
		4'h4: o_wb_data[LGCNT-1:0] <= total_stb_ack;
		4'h5: o_wb_data[LGCNT-1:0] <= simple_acks;
		4'h6: o_wb_data[LGCNT-1:0] <= wait_count;
		//
		4'h7: o_wb_data[LGCNT-1:0] <= hold_count-tail_count;
		4'h8: o_wb_data[LGCNT-1:0] <= tail_count;
		4'h9: o_wb_data[LGCNT-1:0] <= bus_errs;
		4'ha: o_wb_data[LGCNT-1:0] <= bus_aborts;
		4'hb: if (byte_count[LGCNT])
				o_wb_data <= -1;
			else
				o_wb_data[LGCNT-1:0] <= byte_count[LGCNT-1:0];
		4'hc: o_wb_data[LGCNT-1:0] <= write_bytes;
		4'hd: o_wb_data[LGCNT-1:0] <= write_beats;
		4'he: o_wb_data[LGCNT-1:0] <= num_cyc;
		4'hf: o_wb_data <= {
				// pending_idle,
				// pending_first_burst,
				// cleared,
				28'h0, perf_err,
				triggered,
				clear_request,
				start_request
				};
		default: begin end
		endcase
	end

	function [DW-1:0]		apply_sel;
		input	[DW-1:0]	prior_data;
		input	[DW-1:0]	new_data;
		input	[DW/8-1:0]	sel;

		integer	k;
		for(k=0; k<DW/8; k=k+1)
		begin
			apply_sel[k*8 +: 8]
				= sel[k] ? new_data[k*8 +: 8] : prior_data[k*8 +: 8];
		end
	endfunction
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Trigger control & activity counting
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// triggered
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		triggered <= 0;
	else if (idle_bus)
	begin
		if (start_request && !clear_request)
			triggered <= 1'b1;
		if (stop_request)
			triggered <= 0;
	end
	// }}}

	// active_cycles : count number of cycles while triggered
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		active_cycles <= 0;
	else if (triggered)
	begin
		if (!active_cycles[LGCNT])
			active_cycles <= active_cycles + 1;
	end
	// }}}

	// idle_bus : Can we start or stop our couters?  Can't if not idle
	assign	idle_bus = !i_mon_cyc;

	// perf_err
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		perf_err <= 0;
	else if (triggered)
	begin
		if (mon_zero && (!i_mon_stb || i_mon_stall)
						&& (i_mon_ack || i_mon_err))
			perf_err <= 1;
		if (!i_mon_cyc && i_mon_stb)
			perf_err <= 1;
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Statistics
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// General/orthogonal stats
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
	begin
		total_stb <= 0;
		total_stall <= 0;
		total_stb_ack   <= 0;
		total_stall_ack <= 0;
		simple_acks <= 0;
		wait_count  <= 0;
		hold_count  <= 0;
	end else if (!i_mon_cyc || (i_mon_we && !write_en)
				|| (!i_mon_we && !read_en))
	begin
		// DO NOTHING!
	end else if (triggered && i_mon_cyc)
	casez({ i_mon_stb, i_mon_stall, i_mon_ack, mon_zero })
	4'b100?: total_stb   <= total_stb + 1;
	4'b110?: total_stall <= total_stall + 1;
	4'b101?: begin
		total_stb   <= total_stb + 1;
		total_stb_ack   <= total_stb_ack + 1;
		end
	4'b111?: begin
		total_stall     <= total_stall + 1;
		total_stall_ack <= total_stall_ack + 1;
		end
	4'b0?1?: simple_acks <= simple_acks + 1;
	4'b0?00: wait_count  <= wait_count + 1;
	4'b0?01: hold_count  <= hold_count + 1;
	default: begin end
	endcase
	// }}}

	// mon_zero, mon_outstanding
	// {{{
	initial	mon_zero = 1;
	initial	mon_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset || clear_request || !i_mon_cyc || i_mon_err)
	begin
		mon_zero <= 1;
		mon_outstanding <= 0;
	end else case({ i_mon_stb && !i_mon_stall, i_mon_ack })
	2'b10: begin
		mon_outstanding <= mon_outstanding + 1;
		mon_zero <= 0;
		end
	2'b01: begin
		mon_outstanding <= mon_outstanding - 1;
		mon_zero <= (mon_outstanding <= 1);
		end
	default: begin end
	endcase
	// }}}

	// tail_count
	// {{{
	initial	tail_count_aux = 0;
	initial	tail_count = 0;
	always @(posedge i_clk)
	if (i_reset || clear_request || !i_mon_cyc || i_mon_stb || i_mon_ack || i_mon_err)
		tail_count_aux <= 0;
	else if (triggered)
		tail_count_aux <= tail_count_aux + 1;

	always @(posedge i_clk)
	if (i_reset || clear_request)
		tail_count <= 0;
	else if (triggered && !i_mon_cyc && last_cyc)
		tail_count <= tail_count + tail_count_aux;
	// }}}

	// bus_errs, bus_aborts
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		bus_errs <= 0;
	else if (triggered && i_mon_cyc && i_mon_err)
		bus_errs <= bus_errs + 1;

	always @(posedge i_clk)
	if (i_reset || clear_request)
		bus_aborts <= 0;
	else if (triggered && !i_mon_cyc && !mon_zero)
		bus_aborts <= bus_aborts + 1;
	// }}}

	// byte_count
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		byte_count <= 0;
	else if (triggered && i_mon_stb && !i_mon_stall)
	begin
		if (!byte_count[LGCNT]
			&& ((i_mon_we && write_en) || (!i_mon_we && read_en)))
		byte_count <= byte_count + $countones(i_mon_sel);
	end
	// }}}

	// write_bytes
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		write_bytes <= 0;
	else if (triggered && i_mon_stb && !i_mon_stall && i_mon_we)
		write_bytes <= write_bytes + $countones(i_mon_sel);
	// }}}

	// write_beats
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		write_beats <= 0;
	else if (triggered && i_mon_stb && !i_mon_stall && i_mon_we)
		write_beats <= write_beats + 1;
	// }}}

	// num_cyc : Number of times Cyc is activated
	// {{{
	always @(posedge i_clk)
	if (i_reset || clear_request)
		last_cyc <= 1'b0;
	else if (!i_mon_cyc)
		last_cyc <= 1'b0;
	else if (i_mon_stb && ((i_mon_we && write_en)||(!i_mon_we && read_en)))
		last_cyc <= 1'b1;
	else if (write_en && read_en)
		last_cyc <= 1'b1;

	always @(posedge i_clk)
	if (i_reset || clear_request)
		num_cyc <= 0;
	else if (triggered && !i_mon_cyc && last_cyc)
		num_cyc <= num_cyc + 1;
	// }}}


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Simulation report generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Notes:
	// {{{
	// The following is an example report which can be to analyze bus
	// statistics.  It's divided in two parts.  The first part prints out
	// all the various collected data.  All lines in this section are
	// prefixed with "PERF:" to make them easier to identify via grep
	// from a simulation output.  The second half is designed to be
	// cut/copy/pasted into a Matlab or Octave file.  This contains
	// the calculated data summaries for throughput, lag/latency, and
	// efficiency.  The performance monitor doesn't do the actual
	// divide--but rather tells you what numbers need to be divided to
	// achieve the desired performance measures.
	// }}}
	task	report;
		reg [31:0]	num, dnm, cyc_count;
	if (perf_err)
		$display("PERF: BUS ERROR.  INVALID RESULTS.  RESET BUS TO CLEAR.");
	else if (active_cycles[LGCNT])
		$display("PERF: COUNTER OVERFLOW.  TRY AGAIN.");
	else if (total_stb == 0)
		$display("PERF: NO DATA TRANSFERS RECORDED");
	else begin
	$display("PERF: TotalCycles\t0x%08x", active_cycles[LGCNT-1:0]);
	// $display("PERF: CYC cycles\t\t0x%08x",  );
	$display("PERF: TotalSTB\t\t0x%08x",    total_stb);
	$display("PERF: TotalStall\t\t0x%08x",  total_stall);
	$display("PERF: Stall+ACK\t\t0x%08x",   total_stall_ack);
	$display("PERF: STB+ACK\t\t0x%08x",     total_stb_ack);
	$display("PERF: ACK\t\t0x%08x",         simple_acks);
	$display("PERF: Waits\t0x%08x",		wait_count);
	$display("PERF: Holds\t0x%08x",		hold_count-tail_count);
	$display("PERF: TailCount\t\t0x%08x",   tail_count);
	$display("PERF: BusErrs\t\t0x%08x",	bus_errs);
	$display("PERF: BusAborts\t\t0x%08x",	bus_aborts);
	$display("PERF: ByteCount\t\t0x%08x",	byte_count);
	$display("PERF: WriteBytes\t\t0x%08x",  write_bytes);
	$display("PERF: WriteBeats\t\t0x%08x",  write_beats);
	//
	$display("PERF: ---------------------------");
	//
	$display("PERF: ReadBytes\t\t0x%08x",   byte_count-write_bytes);
	$display("PERF: ReadBeats\t\t0x%08x",   total_stb -write_beats);
	//
	cyc_count = total_stb + total_stall + simple_acks + wait_count;

	// num = wr_awr_early + wr_addr_stall + wr_data_lag + wr_addr_lag
	//	+ wr_early_beat + wr_b_lag_count + wr_b_stall_count;
	// dnm = total_stb;
	//
	num = total_stall + wait_count - total_stall_ack;
	dnm = total_stb;
	$display("perf_lag     = %1d / %1d;", num, dnm);
	// num = wr_beat_count;
	// dnm = wr_cycles;
	// dnm = active_time[LGCNT-1:0] - wr_b_end_count - wr_idle_cycles;
	// $display("perf_wreff     = %1d / %1d;", num, dnm);
	num = total_stb;
	dnm = cyc_count;
	$display("perf_eff = %1d / %1d;", num, dnm);

	// num = wr_beat_count;
	// dnm = wr_beat_count + wr_slow_data + wr_stall;
	num = total_stb;
	dnm = total_stb + total_stall;
	$display("perf_thruput = %1d / %1d;", num, dnm);

	//
	// Read lag = wait (ARSTALL + LAG) / # of Bursts
	// num = rd_ar_stalls + rd_lag_counter;
	// dnm = rd_burst_count;
	// $display("perf_rdlag     = %1d / %1d;", num, dnm);
	// num = rd_first_lag;
	// dnm = rd_ar_cycles;
	// $display("perf_rdlatency = %1d / %1d;", num, dnm);
	// num = rd_beat_count;
	// dnm = rd_ar_cycles + rd_ar_stalls + rd_lag_counter + rd_beat_count
	//		+ rd_r_stalls + rd_slow_link;
	// $display("perf_rdeff     = %1d / %1d;", num, dnm);
	// num = rd_beat_count;
	// dnm = rd_slow_link + rd_r_stalls + rd_beat_count;
	// $display("perf_rdthruput = %1d / %1d;", num, dnm);

	end endtask
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data[31:2]
			};
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used in verfiying this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;
`endif
// }}}
endmodule
