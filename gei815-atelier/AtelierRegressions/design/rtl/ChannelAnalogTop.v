//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

module ChannelAnalogTop (
    input clk,
    inout i_waveform,

    input i_AnalogEnable,
    input [7:0] i_DacOffset,
    output [7:0] o_AdcSample
	);

simple_adc u_simple_adc(
    .clk(clk),
    .wave(i_waveform),
    .en(i_AnalogEnable),
    .dout(o_AdcSample)
    );

simple_dac u_simple_dac(
    .clk(clk),
    .din(i_DacOffset),
    .aout(i_waveform)
    );

endmodule
