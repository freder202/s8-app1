//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

`timescale 1ns/10fs

module tb_top();

	wire clk;
	reg reset;

    wire [15:0] userif_SampleData;
    wire userif_SampleRead;
    wire userif_SampleEmpty;

    wrealsum wreal_sig0, wreal_sig1;

	initial begin
		reset = 1;
		@(posedge clk);
		#3;
		reset = 0;
	end


    tb_clockgen u_clockgen(.clk(clk));

    tb_waveformgen u_waveformgen0(.waveform(wreal_sig0));
    tb_waveformgen u_waveformgen1(.waveform(wreal_sig1));

    tb_flowcontrol u_flowcontrol(	.clk(clk),
                                    .uart_in(uart_in),
									.uart_out(uart_out),
									.userif_SampleRead(userif_SampleRead),
									.userif_SampleEmpty(userif_SampleEmpty),
									.userif_SampleData(userif_SampleData)
    );

    OscilloTop u_dut (
	    .reset(reset),
	    .clk(clk),
        .uart_in(uart_in),
        .uart_out(uart_out),
	    .i_waveform_chan0(wreal_sig0),
	    .i_waveform_chan1(wreal_sig1),
		.userif_SampleRead(userif_SampleRead),
		.userif_SampleEmpty(userif_SampleEmpty),
		.userif_SampleData(userif_SampleData)
    );




endmodule
