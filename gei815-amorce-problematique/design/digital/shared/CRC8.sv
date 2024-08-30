/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps

module CRC8 #(parameter
    DATA_LENGTH = 32,
    DATA_LENGTH_BYTES = (DATA_LENGTH/8))(
    input logic clk,
    input logic reset,
    input logic [DATA_LENGTH-1:0] data,
    input logic clear,
    input logic valid,
    output logic [7:0] crc8,
    output logic ready
    );
    typedef enum bit [1:0] {IDLE, CALCULATING, CHECK_COUNT, AWAIT_ACK} states;
    states state;
    localparam logic [7:0] CRC8_Start = 8'h0D;
    localparam logic [7:0] CRC_POLY = 8'hC6;

    int index;
    logic [7:0] r_crc8;

    function automatic logic[7:0] calculate_crc8(input logic [7:0] data_stream, input logic [7:0] crc_current);
        int unsigned j;
        logic [7:0] crc = crc_current;
        for (j=0; j <= 7; j++) // Bitwise from LSB to MSB
            begin
                if ((crc[0]) != (data_stream[j])) begin
                    crc = (crc >> 1) ^ CRC_POLY;
                end else begin
                    crc =  crc >> 1;
                end
            end
            return crc;
    endfunction

    task FSM();
        case (state)
            IDLE: begin
                r_crc8 = CRC8_Start;
                ready <= 0;
                index = 0;
                if (valid) begin
                    state <= CALCULATING;
                end
            end
            CALCULATING: begin
                    r_crc8 = calculate_crc8(data[index*8 +: 8], r_crc8);
                    index ++;
                    state <= CHECK_COUNT;
            end
            CHECK_COUNT: begin
                if (index == DATA_LENGTH_BYTES) begin
                    crc8 = r_crc8;
                    state <= AWAIT_ACK;
                end
                else begin
                    state <= CALCULATING;
                end
            end
            AWAIT_ACK: begin
                ready <= 1;
                if (clear) begin
                    ready <= 0;
                    state <= IDLE;
                end
            end
        endcase
    endtask

    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
        end
        else begin
            FSM();
        end
    end

     

endmodule




