/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps
module counter#(parameter
                BIT_COUNT = 32)
                (input logic clk /* synthesis syn_noclockbuf=1 */,
                input logic enable,
                input logic reset,
                output logic [BIT_COUNT-1:0] count) /* syntheseis hier="hard" */;


    always_ff @ (posedge clk or posedge reset) begin
        if (reset == 1) begin
            count <= 0;
        end
        else if (enable == 1) begin
            count <= count + 1;
        end
    end

endmodule
