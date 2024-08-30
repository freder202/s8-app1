/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

module OverThreshold#(
    parameter resetValue = 1  //parameter
)(
    ThresholdSetterInterface.reader setter,
    input logic [31:0]  signal,
    output logic detect 
);
    logic [31:0] r_threshold;

    // Set the threshold
    always_ff @ (posedge setter.write or posedge setter.reset) begin
        if (setter.reset) begin
            r_threshold <= resetValue;
        end
        else if (setter.write) begin
            r_threshold <= setter.threshold;
        end
    end   
    assign detect = (signal > r_threshold);  
endmodule