/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps
package PacketMergerPackage;
endpackage

module packet_merger #(
    DATA_LENGTH = 8,
    MESSAGE_LENGTH = 48,
    CRC_LENGTH = 8,
    TRANSMISSION_LENGTH = MESSAGE_LENGTH+CRC_LENGTH,
    SEGMENT_COUNT = TRANSMISSION_LENGTH/DATA_LENGTH,
    SEGMENT_COUNT_BITS = $clog2(SEGMENT_COUNT)-1)
    (
    UsartInterface.rx message_if,
    input logic clk,
    input logic reset
);
    typedef enum bit [2:0] {IDLE, RECEIVE_SEGMENTS, CHECK_COUNT, CALCULATE_CRC, VALIDATE_CRC, AWAIT_ACK} states;

    states state;
    logic [SEGMENT_COUNT_BITS:0] segmentCount;
    UartInterface #(8) uart_if();
    logic [TRANSMISSION_LENGTH-1:0] packet ;

    logic crc_clear_r;
    logic crc_valid_r;
    logic crc_last_r;
    logic [CRC_LENGTH-1:0] crc_r;
    logic crc_ready_r;

    wire [7:0] s_uart_data;
    wire s_uart_valid, s_new_uart_valid;

    reg r_uart_ready;

    wire s_crc_match, s_crc_done;

    UartRx inst_rx(.clk(clk),
                .reset(reset),
                .i_serial_in(message_if.sig),
                .i_ready(r_uart_ready),
                .o_data(s_uart_data),
                .o_old_valid(s_uart_valid),
                .o_valid(s_new_uart_valid)
                );

    CRC8816 #(.DATA_LENGTH(MESSAGE_LENGTH)) inst_crc_calc (
        .clk(clk),
        .reset(crc_clear_r),
        .i_data(s_uart_data),
        .i_valid(s_new_uart_valid),
        .i_last(crc_last_r),
        .o_match(s_crc_match),
        .o_done(s_crc_done)
        );

    task FSM();
        case (state)
            IDLE: begin
                message_if.valid <= 0;
                r_uart_ready <= 0;
                crc_clear_r <= 0;
                segmentCount = 0;
                crc_valid_r <= 0;
                if (s_uart_valid) begin
                    state <= RECEIVE_SEGMENTS;
                end
            end
            RECEIVE_SEGMENTS: begin
                if (s_uart_valid) begin
                    packet[segmentCount*8 +: 8] <= s_uart_data; // at index segmentCount*8, insert 8 bits
                    r_uart_ready <= 1;
                    segmentCount++;
                    state <= CHECK_COUNT;
                end
            end
            CHECK_COUNT: begin
                r_uart_ready <= 0;
                if (segmentCount < SEGMENT_COUNT) begin
                    state <= RECEIVE_SEGMENTS;
                end else begin
                    message_if.data <= packet[MESSAGE_LENGTH-1:0];
                    message_if.valid <= 0;
                    state <= VALIDATE_CRC;
                end
            end
            CALCULATE_CRC: begin
                crc_valid_r <= 1;
                state <= VALIDATE_CRC;
            end
            VALIDATE_CRC: begin
            crc_valid_r <= 0;
                if (s_crc_match) begin
                    crc_clear_r <= 1;
                end
                message_if.valid <= s_crc_match;
                state <= AWAIT_ACK;
            end

            AWAIT_ACK: begin
                if (!message_if.valid) begin
                    state <= IDLE;
                end 
                else if (message_if.ready) begin
                    message_if.valid <= 0;
                    state <= IDLE;
                end
            end
        endcase
    endtask
    
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            crc_clear_r <= 1;
            crc_valid_r <= 0;
            r_uart_ready <= 0;
            segmentCount = 0;
            packet <= 0;
        end else begin
            FSM();
        end
    end

    assign message_if.parity_error = 1'b0;

   assign crc_last_r = (segmentCount == (SEGMENT_COUNT - 1));
endmodule
