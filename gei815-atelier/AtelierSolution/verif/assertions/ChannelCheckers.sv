//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


// Bind statement usage in mixed-langage environments
//			https://www.youtube.com/watch?v=VuBqJoTRYyU


// Direct mapping of VHDL generics doesn't work. Skip channel number property for now
//bind ChannelDigitalTop ChannelCheckers #(.g_ChannelId(g_ChannelId)) u_ChannelCheckers(.*);
bind ChannelDigitalTop ChannelCheckers u_ChannelCheckers(
	.clk(clk),
	.i_MasterEnable(i_MasterEnable),
	.i_AdcSample(i_AdcSample),
	.s_ChannelEnable(s_ChannelEnable),
	.s_AnalogEnable(s_AnalogEnable),
	.s_SignalTriggerMasked(s_SignalTriggerMasked),
	.s_FifoHalfFull(s_FifoHalfFull),
	.r_AdcStringWrite(r_AdcStringWrite),
	.r_SignalTrigger(r_SignalTrigger),
	.r_CountSamples(r_CountSamples),
	.r_AdcString(r_AdcString)
	);


module ChannelCheckers
	//#(parameter g_ChannelId = 15)
	(
	input clk,
	input i_MasterEnable,
	input [7:0] i_AdcSample,
	input s_ChannelEnable,
	input s_AnalogEnable,
	input s_SignalTriggerMasked,
	input s_FifoHalfFull,
	input r_AdcStringWrite,
	input r_SignalTrigger,
	input [7:0]  r_CountSamples,
	input [15:0] r_AdcString
	);


default clocking DEFCLK @(posedge clk);
endclocking


// check that analog enable comes before digital enable
property p_analog_enable_before_digital;
	i_MasterEnable & s_ChannelEnable |-> s_AnalogEnable;
endproperty
ast_analog_enable_before_digital : assert property(p_analog_enable_before_digital);

//ast2_analog_enable_before_digital : assert property(p_analog_enable_before_digital)
//		$display("custom pass message");
//	else begin
//		$display("custom fail message.");
//		$display("Do something else.");
//	end

// Channel masked signal shouldn't rose if either master or channel enable are off
property p_both_enables_for_trigger;
	s_SignalTriggerMasked |-> i_MasterEnable & s_ChannelEnable;
endproperty
ast_both_enables_for_trigger : assert property(p_both_enables_for_trigger);

// Start writing on next cycle if trigger happens
property p_trigger_starts_sample_write;
	$rose(s_SignalTriggerMasked) and r_CountSamples == 8'hf |=> r_AdcStringWrite[*16];
endproperty
ast_trigger_starts_sample_write : assert property(p_trigger_starts_sample_write);

// if trigger doesn't occur exactly at the 16th write, then write should stop
property p_sample_write_stop_if_no_pileup;
	$rose(s_SignalTriggerMasked) ##1 r_AdcStringWrite[*16] ##0 !s_SignalTriggerMasked |=> !r_AdcStringWrite;
endproperty
ast_sample_write_stop_if_no_pileup : assert property(p_sample_write_stop_if_no_pileup);

// check triggering conditions are on rising edge. Use $past to account for shift register
property p_scope_trigger;
	$rose(r_SignalTrigger) |-> ($past(i_AdcSample, 3) < $past(i_AdcSample, 2));
endproperty
ast_scope_trigger : assert property(p_scope_trigger);

// check that trigger happens only when fifo is not half full
property p_scope_trigger_fifo_avail;
	$rose(r_SignalTrigger) |-> $past(!s_FifoHalfFull, 1);
endproperty
ast_scope_trigger_fifo_avail : assert property(p_scope_trigger_fifo_avail);


//todo - find way to bind with hierarchical properties in mixed langage.
/*
// first data item is channel address
property p_first_data_is_address;
	$rose(r_AdcStringWrite) |-> (r_AdcString[7:0] = g_ChannelId);
endproperty
ast_first_data_is_address : assert property(p_first_data_is_address);
*/

endmodule
