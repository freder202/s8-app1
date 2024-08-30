/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

import TDCTypes::*;



module TDC_dumb
    #(parameter
    TDC_CHANNEL channelNumber = CHAN_0
    )
    (// Ports declaration
        TDCInterface.internal bus,
        input                 clk,
        input                 trigger
    );

    // local variable
    reg [31:0] clk_counter;
    reg [31:0] valeur_TOT;
    reg [31:0] valeur_Time;
    assign bus.chan = channelNumber;

    always_ff @(posedge clk, posedge bus.clear) begin
        if (bus.clear) begin
                clk_counter <= 0;
                bus.hasEvent <= 0;
                bus.timestamp <= 0;
                bus.timeOverThreshold <= 0;
                valeur_TOT <= 199099;
                valeur_Time <= 25505;
            end
        else if (!bus.hasEvent & trigger) begin
                if (clk_counter == 10000) begin
                // Random values
                //valeur_TOT++;
                //valeur_Time++;
                bus.timestamp <= valeur_Time;//$urandom();
                bus.timeOverThreshold <= valeur_TOT;//$urandom();
                bus.hasEvent <= 1;
                clk_counter <= 0;
            end
            clk_counter <= clk_counter + 1;
        end

    end
    
endmodule // TDC_dumb

