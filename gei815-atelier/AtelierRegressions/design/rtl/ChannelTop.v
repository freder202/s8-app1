//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

module ChannelTop(
    input reset,
	input clk,

	input i_waveform,

    input  [1:0] i_Mode,
    input  [5:0] i_Addr,
    input  [7:0] i_DataIn,
    output [7:0] o_DataOut,

	input  i_MasterEnable,

	input  i_ReadSample,
	output o_ReadSampleEmpty,
    output [15:0] o_ReadSampleData
	);

parameter g_ChannelId = 1 ;

wire [7:0] dacvalue;
wire [7:0] s_AdcSample;

ChannelAnalogTop u_ChannelAnalogTop(
	.clk(clk),
    .i_waveform(i_waveform),

    .i_AnalogEnable(analogenable),
    .i_DacOffset(dacvalue),
    .o_AdcSample(s_AdcSample)
	);

ChannelDigitalTop #(.g_ChannelID(g_ChannelId)) u_ChannelDigitalTop(
    .reset(reset),
	.clk(clk),

    .i_Mode(i_Mode),
    .i_Addr(i_Addr),
    .i_DataIn(i_DataIn),
    .o_DataOut(o_DataOut),

	.i_AdcSample(s_AdcSample),

	.i_ReadSample(i_ReadSample),
	.o_ReadSampleEmpty(o_ReadSampleEmpty),
    .o_ReadSampleData(o_ReadSampleData),

	.i_MasterEnable(i_MasterEnable),
    .o_AnalogEnable(analogenable),
    .o_DacValue(dacvalue)
    );



endmodule
