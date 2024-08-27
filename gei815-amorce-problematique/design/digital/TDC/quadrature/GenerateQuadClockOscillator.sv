 /*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
 
 `timescale 1ps/1ps
module GenerateQuadClock #(parameter BIT_COUNT = 32)(
    input logic clk,
    input logic reset,
    output logic clkQuad    
);

    logic r_cycle;
    logic r_clk0, r_clk45, r_clk90, r_clk135;
    // Get 4 clock dephase to eachother by 45 degrees
    ClockDephasedGenerator clkGenerator (.clk(clk), .clk0(r_clk0), .clk45(r_clk45), .clk90(r_clk90), .clk135(r_clk135));
    
    assign clkQuad = r_cycle;
    //Xor the value of the clock. 
    assign r_cycle = r_clk0^r_clk45^r_clk90^r_clk135;
    

endmodule
