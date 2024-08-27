/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
// Simple counter into gray code. 
`timescale 1ps/1ps
module gray_counter
  #(parameter BIT_COUNT=32)
  ( input logic clk,     
    input logic enable,           
    input logic reset,
    output logic [BIT_COUNT-1:0] count);    
   
  logic [BIT_COUNT-1:0] counter;

  counter #(.BIT_COUNT(BIT_COUNT)) grayCounter(.clk(clk), .enable(enable), .reset(reset), .count(counter));
   
  always_comb begin
  foreach (counter[i]) 
    count[i-1] = counter[i]^counter[i-1]; 
    
  count[BIT_COUNT-1] = counter[BIT_COUNT-1];
  end  
  
endmodule