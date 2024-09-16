//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind TDC_dumb TDCCoverage inst_TDCCoverage(
	.cov_reset(reset),
	.cov_clk(clk),
	.cov_hasEvent(o_hasEvent),
	.cov_busy(o_busy),
	.cov_clear(i_clear),
	.cov_trigger(i_trigger),
	.cov_enable(i_enable_channel),
	.cov_TOT(o_pulseWidth),
	.cov_TS(o_timestamp)
	);

module TDCCoverage
	
	(
	input logic cov_reset,
	input logic cov_clk,
    	input logic cov_hasEvent,
	input logic cov_busy,
	input logic cov_clear,
    	input logic cov_trigger,
	input logic cov_enable,
	input logic [31:0] cov_TOT,
	input logic [31:0] cov_TS
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

//ASSERTS
//TDC.1.4	When reset = 1, o_busy = 0

//TDC.1.5	When reset = 1, o_hasEvent = 0

//TDC4.2	When i_trigger = 1, in the next 2 clock MUST o_busy = 1	Assert(prop)	Cover(prop)	Global

//TDC4.3	If i_enable = 1 When i_trigger = 1, on the next clock o_busy = 1	Assert(prop)	Cover(prop)	Global

//TDC4.4	Can only be deasserted after o_hasEvent have been deasserted first (1 clock after)	Assert(prop)	Cover(prop)	Global

//TDC5.2	if o_hasEvent = 0 when asserted, o_busy and o_hasEvent do not change state	Assert(prop)	Cover(prop)	Global

//TDC6.3	Do not change state if i_enable = 0 unless on a reset = 1	Assert(prop)	Cover(prop)	S.D

//TDC7.2	Do not change state if i_enable = 0 unless it's a reset	Assert(prop)	Cover(prop)	S.D

//TDC7.4	if i_clear = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global

//TDC7.5	if reset = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global

//TDC8.5	if i_clear = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global

//TDC8.6	if reset = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global


//COVERPOINTS
// TDC.1.1	When reset = 1, i_trigger is toggled	N/A	cross @ reset
// TDC.1.2	When reset = 1, i_enable_channel is toggled	N/A	cross @ reset
// TDC.1.3	When reset = 1, i_clear is toggled	N/A	cross @ reset
// TDC.1.6	Must have reached value 1 at least once	N/A	Coverpoint @ clk


//i_trigger TDC.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//i_enable_channel TDC3.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//o_busy TDC.4.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//i_clear TDC5.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//o_hasEvent TDC6.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//o_timestamp TDC7.1	Check  a variety of values	N/A	Bins @ clk
//o_pulseWidth TDC8.2	check a variety of value between 0 and 125000	N/A	Bins @ clk




//TDC3.2	When i_enable_channel = 0, i_trigger is toggled	N/A	cross @ i_enable_channel
//TDC3.3	When i_enable_channel = 0, i_enable_channel is toggled	N/A	cross @ i_enable_channel
//TDC3.4	When i_enable_channel = 0, i_clear is toggled	N/A	cross @ i_enable_channel
//bin enable = 0 @clk reset = 0

endmodule
