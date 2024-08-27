`timescale 1ps/1ps

module SimTimeDiff #(parameter BIT_COUNT = 32)(
    input logic enable,
    output logic [BIT_COUNT-1:0] count,
    output logic hasValue    
);

    logic [BIT_COUNT-1:0] r_count;
    int timeOfRise;

    always_ff @(posedge enable or negedge enable) begin
        if (enable) begin
            timeOfRise <= int'($time);
            hasValue <= 0;
            count <= 0;
        end
        else begin
            count <= int'($time) - timeOfRise;
            hasValue <= 1;
        end
    end
endmodule