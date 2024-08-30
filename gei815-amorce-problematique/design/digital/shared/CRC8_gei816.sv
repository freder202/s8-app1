/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps

module CRC8816 #(parameter
    DATA_LENGTH = 32,
    DATA_LENGTH_BYTES = (DATA_LENGTH/8))(
    input logic clk,
    input logic reset,
    input logic i_valid,
    input logic i_last,
    input logic [7:0] i_data,
    output logic o_match,
    output logic o_done,
    output logic [7:0] o_crc8
    );
    typedef enum bit [1:0] {IDLE, CALCULATING, CHECK_CRC, AWAIT_ACK} states;
    states state;
    localparam logic [7:0] CRC8_Start = 8'h0D;
    localparam logic [7:0] CRC_POLY = 8'hC6;
    localparam logic [7:0] CRC_MATCH_VALUE = 8'h00;

    int index;
    logic [7:0] r_crc8;
    reg r_done;
    reg r_match;

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
                index = 0;
                r_match = 0;
                r_done = 0;
                state <= CALCULATING;

            end
            CALCULATING: begin
                if (i_valid) begin
                    r_crc8 = calculate_crc8(i_data, r_crc8);
                end

                if (i_valid && i_last) begin
                    state <= CHECK_CRC;
                end
                else begin
                    state <= CALCULATING;
                end
            end
            CHECK_CRC: begin
                if (r_crc8 == CRC_MATCH_VALUE) begin
                    r_match = 1;
                end
                else begin
                    r_match = 0;
                end
                r_done = 1;
                state <= AWAIT_ACK;
            end
            AWAIT_ACK: begin
                state <= AWAIT_ACK;
            end
        endcase
    endtask

    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            r_match = 0;
            r_done = 0;
        end
        else begin
            FSM();
        end
    end

     assign o_match = r_match;
     assign o_done = r_done;
     assign o_crc8 = r_crc8;

endmodule




