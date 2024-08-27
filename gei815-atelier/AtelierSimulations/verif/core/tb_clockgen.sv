//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps

module tb_clockgen(clk);

    output clk;
    reg clk;

    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk; // generate a clock
    end

endmodule
