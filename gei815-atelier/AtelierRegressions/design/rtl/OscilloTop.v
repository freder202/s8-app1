//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

module OscilloTop(
    input reset,
	input clk,

    input uart_in,
    output uart_out,

	inout i_waveform_chan0,
	inout i_waveform_chan1,

    input userif_SampleRead,
    output userif_SampleEmpty,
    output [15:0] userif_SampleData
);



wire [1:0] reg_mode;
wire [5:0] reg_addr;
wire [7:0] reg_datain;
wire [7:0] reg_dataout;

wire [7:0] reg_dataout_chan0;
wire [7:0] reg_dataout_chan1;

wire [15:0] s_ReadSampleData_chan0;
wire [15:0] s_ReadSampleData_chan1;

wire [15:0] s_ReadSampleData;

ChannelTop #(0) u_channeltop0 (
    .reset(reset),
    .clk(clk),

    .i_Mode(reg_mode),
    .i_Addr(reg_addr),
    .i_DataIn(reg_datain),
    .o_DataOut(reg_dataout_chan0),

	.i_MasterEnable(s_MasterEnable),
    .i_waveform(i_waveform_chan0),

	.i_ReadSample(s_ReadSample_chan0),
	.o_ReadSampleEmpty(s_ReadSampleEmpty_chan0),
    .o_ReadSampleData(s_ReadSampleData_chan0)
	);

ChannelTop #(1) u_channeltop1 ( // todo why #(.g_ChannelID(1)) doesn't work?
    .reset(reset),
    .clk(clk),

    .i_Mode(reg_mode),
    .i_Addr(reg_addr),
    .i_DataIn(reg_datain),
    .o_DataOut(reg_dataout_chan1),

	.i_MasterEnable(s_MasterEnable),
    .i_waveform(i_waveform_chan1),

	.i_ReadSample(s_ReadSample_chan1),
	.o_ReadSampleEmpty(s_ReadSampleEmpty_chan1),
    .o_ReadSampleData(s_ReadSampleData_chan1)
	);


// mux for register data readback
assign reg_dataout = (reg_addr[4]) ? reg_dataout_chan1 : reg_dataout_chan0;
assign s_ReadSampleData = (s_ReadSample_chan1) ? s_ReadSampleData_chan1 : s_ReadSampleData_chan0;

CommonModules u_commonmodules (
    .reset(reset),
    .clk(clk),

    .reg_Mode(reg_mode),
    .reg_Addr(reg_addr),
    .reg_DataIn(reg_datain),
    .reg_DataOut(reg_dataout),

    .chan_ReadSample0(s_ReadSample_chan0),
    .chan_ReadSample1(s_ReadSample_chan1),
    .chan_ReadSampleEmpty0(s_ReadSampleEmpty_chan0),
    .chan_ReadSampleEmpty1(s_ReadSampleEmpty_chan1),
    .chan_ReadSampleData(s_ReadSampleData),

    .uart_in(uart_in),
    .uart_out(uart_out),

    .userif_Mode(2'b0),
    .userif_Addr(6'b0),
    .userif_DataIn(8'h0),
    .userif_DataOut(),
    .userif_SampleRead(userif_SampleRead),
    .userif_SampleEmpty(userif_SampleEmpty),
    .userif_SampleData(userif_SampleData),

    .o_MasterEnable(s_MasterEnable)

    );


endmodule
