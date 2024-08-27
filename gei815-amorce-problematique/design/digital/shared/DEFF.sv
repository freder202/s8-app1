 /*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
// This module is used to reverse the value of a signal using two flipflop. This can work with a clock also.
// This code is pretty similar to the one found in stackOverflow. 

module DEFF (
    input clk, rst, in,
    output out
);

reg reg1, reg2;

  assign out = trig1^trig2;

  always @(posedge clk, posedge rst) begin
    if (rst)  reg1 <= 0;
    else  reg1 <= in^reg2;
  end

  always @(negedge clk, posedge rst) begin
    if (rst)  reg2 <= 0;
    else  reg2 <= in^reg1;
  end
endmodule