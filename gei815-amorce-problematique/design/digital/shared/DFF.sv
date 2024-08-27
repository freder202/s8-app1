`timescale 1ps/1ps

module DFF( input logic clk, D, rst,
            output logic Q);

always_ff @(posedge clk or posedge rst)
begin
    if (rst) begin
        Q <= 0;
    end
    else begin
        Q <= D;
    end
end
endmodule