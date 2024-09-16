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
//TDC1.4	When reset = 1, o_busy = 0
property p_TDC1_4;
	@(posedge cov_clk)
	$rose(cov_reset) |=> (cov_busy == 0);
endproperty
ast_TDC1_4 : assert property(p_TDC1_4);
cov_TDC1_4 : cover property(p_TDC1_4);

//TDC1.5	When reset = 1, o_hasEvent = 0
property p_TDC1_5;
	@(posedge cov_clk)
	$rose(cov_reset) |=> (cov_hasEvent == 0);
endproperty
ast_TDC1_5 : assert property(p_TDC1_5);
cov_TDC1_5 : cover property(p_TDC1_5);

//TDC4.2	When i_trigger = 1, in the next 2 clock MUST cov_busy = 1	Assert(prop)	Cover(prop)	Global
property p_TDC4_2;  
	@(posedge cov_clk) disable iff (cov_reset)
	$rose(cov_trigger) |-> ##2 (cov_busy == 0);
endproperty
ast_TDC4_2 : assert property(p_TDC4_2);
cov_TDC4_2 : cover property(p_TDC4_2);

//TDC4.3	If i_enable = 1 When i_trigger = 1, on the next clock o_busy = 1	Assert(prop)	Cover(prop)	Global
property p_TDC4_3;
	@(posedge cov_clk) disable iff (cov_reset)
	$rose(cov_enable) |=> (cov_busy == 1);
endproperty
ast_TDC4_3 : assert property(p_TDC4_3);
cov_TDC4_3 : cover property(p_TDC4_3);

//TDC4.4	Can only be deasserted after o_hasEvent have been deasserted first (1 clock after)	Assert(prop)	Cover(prop)	Global
property p_TDC4_4_1;
	@(posedge cov_clk) disable iff (cov_reset)
	$fell(cov_hasEvent) |=> $fell(cov_busy);
endproperty
ast_TDC4_4_1 : assert property(p_TDC4_4_1);
cov_TDC4_4_1 : cover property(p_TDC4_4_1);

property p_TDC4_4_2;
	@(posedge cov_clk) disable iff (cov_reset)
	$stable(cov_hasEvent) |=> $stable(cov_busy);
endproperty
ast_TDC4_4_2 : assert property(p_TDC4_4_2);
cov_TDC4_4_2 : cover property(p_TDC4_4_2);

//TDC5.2	if o_hasEvent = 0 when asserted, o_busy and o_hasEvent do not change state	Assert(prop)	Cover(prop)	Global
property p_TDC5_2_1;
	@(posedge cov_clk) disable iff (cov_reset)
	($rose(cov_clear) && (cov_hasEvent == 0)) |=> $stable(cov_busy);
endproperty
ast_TDC5_2_1 : assert property(p_TDC5_2_1);
cov_TDC5_2_1 : cover property(p_TDC5_2_1);

property p_TDC5_2_2;
	@(posedge cov_clk) disable iff (cov_reset)
	($rose(cov_clear) && (cov_hasEvent == 0)) |=> $stable(cov_hasEvent);
endproperty
ast_TDC5_2_2 : assert property(p_TDC5_2_2);
cov_TDC5_2_2 : cover property(p_TDC5_2_2);

//TDC6.3	Do not change state if i_enable = 0 unless on a reset = 1	Assert(prop)	Cover(prop)	S.D
property p_TDC6_3;
	@(posedge cov_clk) disable iff (cov_reset)
	(cov_enable == 0) |=> $stable(cov_hasEvent);
endproperty
ast_TDC6_3 : assert property(p_TDC6_3);
cov_TDC6_3 : cover property(p_TDC6_3);

//TDC7.2	Do not change state if i_enable = 0 unless it's a reset	Assert(prop)	Cover(prop)	S.D
property p_TDC7_2;
	@(posedge cov_clk) disable iff (cov_reset)
	(cov_enable == 0) |-> $stable(cov_TS);
endproperty
ast_TDC7_2 : assert property(p_TDC7_2);
cov_TDC7_2 : cover property(p_TDC7_2);


//TDC7.4	if i_clear = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)
property p_TDC7_3;
	@(posedge cov_clk) disable iff (cov_reset)
	$rose(cov_hasEvent) |-> ($past(cov_TS, 1) != (cov_TS));
endproperty
ast_TDC7_3 : assert property(p_TDC7_3);
cov_TDC7_3 : cover property(p_TDC7_3);

//TDC7.4	if i_clear = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global
property p_TDC7_4;
	@(posedge cov_clk) disable iff (cov_reset)
	$rose(cov_clear) |-> $stable(cov_TS);
endproperty
ast_TDC7_4 : assert property(p_TDC7_4);
cov_TDC7_4 : cover property(p_TDC7_4);

//TDC7.5	if reset = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global
property p_TDC7_5;
	@(posedge cov_clk) disable iff (!cov_reset)
	$rose(cov_reset) |-> $stable(cov_TS);
endproperty
ast_TDC7_5 : assert property(p_TDC7_5);
cov_TDC7_5 : cover property(p_TDC7_5);

//TDC8.5	if i_clear = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global
property p_TDC8_5;
	@(posedge cov_clk) disable iff (cov_reset)
	$rose(cov_clear) |-> $stable(cov_TOT);
endproperty
ast_TDC8_5 : assert property(p_TDC8_5);
cov_TDC8_5 : cover property(p_TDC8_5);

//TDC8.6	if reset = 1 do not change state on the next clock cycle	Assert(prop)	Cover(prop)	Global
property p_TDC8_6;
	@(posedge cov_clk) disable iff (!cov_reset)
	$rose(cov_reset) |-> $stable(cov_TOT);
endproperty
ast_TDC8_6 : assert property(p_TDC8_6);
cov_TDC8_6 : cover property(p_TDC8_6);

//COVERPOINTS
// TDC1.1	When reset = 1, i_trigger is toggled	N/A	cross @ reset
// TDC1.2	When reset = 1, i_enable_channel is toggled	N/A	cross @ reset
// TDC1.3	When reset = 1, i_clear is toggled	N/A	cross @ reset
// TDC1.6	Must have reached value 1 at least once	N/A	Coverpoint @ clk
covergroup covg_TDC_reset_cross
    @(posedge cov_clk iff cov_reset);
	option.name = "cross_reset_1";
	reset : coverpoint cov_reset {bins bin[] = {1};}
	i_trigger : coverpoint cov_trigger {bins bin[] = {[0:1]};}
	i_enable_channel : coverpoint cov_enable {bins bin[] = {[0:1]};}
	i_clear : coverpoint cov_clear {bins bin[] = {[0:1]};}
	reset_trigger : cross reset, i_trigger;
	reset_enable : cross reset, i_enable_channel;
	reset_clear : cross reset, i_clear;
endgroup
covg_TDC_reset_cross cov_TDC_reset_cross = new();


//i_trigger TDC.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//i_enable_channel TDC3.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//o_busy TDC.4.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//i_clear TDC5.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//o_hasEvent TDC6.1	Must have reached value 1 at least once when reset not asserted	N/A	Coverpoint @ clk
//o_timestamp TDC7.1	Check  a variety of values	N/A	Bins @ clk
//o_pulseWidth TDC8.2	check a variety of value between 0 and 125000	N/A	Bins @ clk
covergroup covg_TDC_base_coverage
	@(posedge cov_clk iff (!cov_reset));
	option.name = "cross_enable_0";
	i_trigger : coverpoint cov_trigger;
	i_enable_channel : coverpoint cov_enable;
	o_busy : coverpoint cov_busy;
	i_clear : coverpoint cov_clear;
	o_hasEvent : coverpoint cov_hasEvent;
	o_timestamp : coverpoint cov_TS {bins bin[] = {[0:4294967295]};}
	o_pulseWidth : coverpoint cov_TOT {bins bin[] = {[0:125000]};}
endgroup
covg_TDC_base_coverage cov_TDC_base_coverage = new();

//TDC3.2	When i_enable_channel = 0, i_trigger is toggled	N/A	cross @ i_enable_channel
//TDC3.3	When i_enable_channel = 0, i_enable_channel is toggled	N/A	cross @ i_enable_channel
//TDC3.4	When i_enable_channel = 0, i_clear is toggled	N/A	cross @ i_enable_channel
//bin enable = 0 @clk reset = 0
covergroup covg_TDC_cross_enable
	@(posedge cov_clk iff (!cov_reset));
	option.name = "cross_enable_0";
	reset : coverpoint cov_reset {bins bin[] = {1};}
	i_trigger : coverpoint cov_trigger {bins bin[] = {[0:1]};}
	i_enable_channel : coverpoint cov_enable {bins bin[] = {1};}
	i_clear : coverpoint cov_clear {bins bin[] = {[0:1]};}
	enable_trigger : cross i_enable_channel, i_trigger;
	enable_clear : cross i_enable_channel, i_clear;


endgroup
covg_TDC_cross_enable cov_TDC_cross_enable = new();

endmodule
