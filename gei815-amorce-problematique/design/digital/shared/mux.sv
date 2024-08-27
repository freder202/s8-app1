/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps
module mux #(WIDTH = 16,
             DATA_LENGTH = 68)
            // Ports declaration
               (input logic [$clog2(WIDTH) - 1 : 0] sel, // Selection goes from 0 to 16. 0 return nothing
                input logic [DATA_LENGTH - 1:0] i_data[WIDTH],              
                output wire [DATA_LENGTH-1:0]   o_data);
    
        //logic [$clog2(WIDTH):0] sel2addr;
        //logic [$clog2(WIDTH)-1:0] resized_sel;
        
        assign o_data = i_data[sel];
        
        /*always @(sel) begin
            if (sel != 0) begin
                sel2addr = sel-1;
                resized_sel = sel2addr[$clog2(WIDTH)-1:0];
            end
        end*/

        /*generate
            for (genvar i=0; i<WIDTH; i++) begin
                assign o_data = sel == i + 1 ? i_data[i] : 'z;
                assign o_available = sel == i + 1 ? 1 : 'z;
            end
        endgenerate*/
        
endmodule // TDC_output_control
