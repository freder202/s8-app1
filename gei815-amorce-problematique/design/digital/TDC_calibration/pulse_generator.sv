/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps
module pulse_generator #(parameter CLK_CNT=10)( 
    input logic trigger,
    input logic clk,
    input logic reset,
    output logic pulse);
    
typedef enum bit {IDLE, PULSING} states;
states state;

logic [7:0] clk_counter;
logic enable, clear;

counter #(8) cnt(clk, enable, clear, clk_counter);
DFF trig (trigger, 1'b1, clear, enable);
assign pulse = clk_counter != 0;

always_ff @(posedge clk) begin
    if (reset) begin
        clear <= 1;
    end else begin
        if (clk_counter == CLK_CNT) begin
            clear <= 1;
        end else begin
            clear <= 0;
        end
    end
end
endmodule

