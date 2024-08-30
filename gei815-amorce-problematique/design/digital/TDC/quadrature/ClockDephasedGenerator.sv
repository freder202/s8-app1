 /*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

module ClockDephasedGenerator #(parameter 
                                    period_ps=12,
                                    DELAY_CLK90=period_ps/4,
                                    DELAY_CLK180=period_ps/2,
                                    DELAY_CLK270=DELAY_CLK90 + DELAY_CLK180)(
    input clk,
    output logic clk0,
    output logic clk45,
    output logic clk90,
    output logic clk135
    )/* synthesis syn_noprune = 1 */;
    logic clk_r;
    generate
    `ifndef LIBERO
        //Generate 4 clocks using a primitive. See the smartDesign named DephasedClockGen
        DephasedClockGen clkGen(.clkMHz(clk), .clkOne(clk0), .clkTwo(clk45), .clkThree(clk90), .clkFour(clk135));
    `else
        // Only for sims with Cadence. Doesn't work for verilator. 
        #(DELAY_CLK90)(clk, clk90);
        #(DELAY_CLK180)(clk, clk180);
        #(DELAY_CLK270)(clk, clk270);
    `endif
            
    endgenerate;
endmodule