//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


// Bind statement usage in mixed-langage environments
//			https://www.youtube.com/watch?v=VuBqJoTRYyU


bind ChannelDigitalTop ChannelCoverage u_ChannelCoverage(
	.reset(reset),
	.clk(clk),
	.i_MasterEnable(i_MasterEnable),
	.s_ChannelEnable(s_ChannelEnable),
	.s_ReadSampleEmpty(s_ReadSampleEmpty),
	.s_SignalTriggerMasked(s_SignalTriggerMasked),
	.s_DacValue(s_DacValue),
	.s_SamplingThreshold(s_SamplingThreshold),
	.s_SamplesOffset(s_SamplesOffset)
	);


module ChannelCoverage
	//#(parameter g_ChannelId = 15)
	(
	input reset,
	input clk,
	input i_MasterEnable,
	input s_ChannelEnable,
	input s_ReadSampleEmpty,
	input s_SignalTriggerMasked,
	input [7:0] s_DacValue,
	input [7:0] s_SamplingThreshold,
	input [7:0] s_SamplesOffset
	);


default clocking DEFCLK @(posedge clk);
endclocking



// Check that something is the fifo a few clocks after at trigger
property p_fifo_not_empty_after_trigger;
	$rose(s_SignalTriggerMasked) |-> ##[1:4] $fell(s_ReadSampleEmpty);
endproperty
cov_fifo_not_empty_after_trigger : cover property(p_fifo_not_empty_after_trigger);



// Check all combinations of channel and master enable (uses cross).
covergroup covg_ChanEnables @(posedge clk iff !reset);
	option.name		= "cov_enableCombinations";
    chanEnable     : coverpoint s_ChannelEnable;
    masterEnable   : coverpoint i_MasterEnable;

    enableCombinations : cross chanEnable, masterEnable;
endgroup
covg_ChanEnables cov_ChanEnables = new();



// Create covergroup for configuration registers. Ensures that different ranges
// of values were simulated.
// Use a specific sampling condition to capture coverage.
covergroup covg_ChanConfigurations
	@(posedge clk iff (i_MasterEnable == 1'b1 && s_ChannelEnable == 1'b1 && s_SignalTriggerMasked == 1'b1));
	option.name		= "cov_ChannelConfigurations";


    dacValues   : coverpoint s_DacValue;
    threshold   : coverpoint s_SamplingThreshold {
		ignore_bins zero_value = {0};
	}

	samplingOffset : coverpoint s_SamplesOffset {
		bins default_value	= {4};
		bins low_range		= {0,6};
		bins mid_range		= {7,19};
		bins high_range		= {20, 31};
	}
endgroup

covg_ChanConfigurations cov_ChanConfigurations = new();



////////////////////////////////////////////////////////////////////////////
// Alternate sampling method for more customizations
// remove line 63 (but keep semicolon) and uncomment the next section.
////////////////////////////////////////////////////////////////////////////
//initial begin
//    cov_ChanConfigurations.start();
//end
//
//	always @(posedge clk)
//	    if(i_MasterEnable == 1'b1 && s_ChannelEnable == 1'b1 && s_SignalTriggerMasked == 1'b1)
//			cov_ChanConfigurations.sample();
////////////////////////////////////////////////////////////////////////////


endmodule
