/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps
module differential_pulse(  input logic start, stop,
                            output logic signal);

always_ff @(posedge start or posedge stop) begin
    if (stop) begin
        signal <= 0;
    end else if (start) begin
        signal <= 1;
    end
end

//<statements>

endmodule