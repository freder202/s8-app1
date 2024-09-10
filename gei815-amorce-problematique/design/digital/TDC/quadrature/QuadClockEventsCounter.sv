 /*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
 
 `timescale 1ps/1ps
module OscillatorQuadrature #(parameter BIT_COUNT = 32)(
    input logic clk,
    input logic enable, reset,
    output logic [BIT_COUNT-1:0] count,
    output logic hasValue    
)/* synthesis syn_noprune = 1 */;
    logic r_signalEnd;
    logic [BIT_COUNT-1:0] r_gray_count; 
    logic [BIT_COUNT-1:0] r_count;
    logic r_clkQuad;
    
    // Gray counter
    gray_counter oscillatorCounter (.enable(enable), .clk(r_clkQuad), .reset(reset), .count(r_gray_count));
    
    // Convert gray to bin
    gray2bin grayConverter (.gray(r_gray_count), .bin(r_count));
    
    // Generate a clock from a 50MHz clock
    GenerateQuadClock quadClock(.clk(clk), .reset(reset), .clkQuad(r_clkQuad));
    
    assign r_signalEnd = !enable;
    assign count = r_count;

    always_ff @( posedge enable or posedge r_signalEnd) begin
        if (enable) begin
            hasValue <= 0;
        end
        else if (r_signalEnd) begin
            hasValue <= 1;
        end
    end

endmodule
