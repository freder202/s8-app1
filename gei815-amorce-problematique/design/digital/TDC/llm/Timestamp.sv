/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

`timescale 1ps/1ps
module Timestamp #(parameter BIT_COUNT=32)(
    input logic reset,
    input logic clock,
    output logic [BIT_COUNT-1:0] timestamp);

    /* verilator lint_off PINMISSING */
    Oscillator #(.BIT_COUNT(BIT_COUNT), .IS_TIMESTAMP(1)) oscillator (.enable(1'b1), .reset(reset), .count(timestamp), .hasValue( ));
    /* lint_on */
    
    //counter timer (.clk(clk), .enable(1), .reset(reset), .count(timestamp));


endmodule