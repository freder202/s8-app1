/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ps/1ps
//import USARTPackage::*;

module packet_splitter #(parameter
    DATA_LENGTH = 8,
    MESSAGE_LENGTH = 48,
    CRC_LENGTH = 8,
    SEGMENT_COUNT = MESSAGE_LENGTH/DATA_LENGTH,
    SEGMENT_COUNT_BITS = $clog2(SEGMENT_COUNT)-1)
    (
    UsartInterface.tx _tx,
    input logic clk,
    input logic reset
);

typedef enum bit[2:0] {IDLE, SEND_SEGMENT, AWAIT_SEGMENT_ACK, SEND_CRC, AWAIT_CRC_ACK, CHECK_COUNT} states;

states state;
logic [SEGMENT_COUNT_BITS:0] segmentCount;
UartInterface #(8) uart();
logic [DATA_LENGTH-1:0] segments [SEGMENT_COUNT-1:0];

logic crc_clear_r;
logic crc_valid_r;
logic [CRC_LENGTH-1:0] crc_r;
logic crc_ready_r;

UartTx tx(uart.tx, clk, !reset);

CRC8 #(.DATA_LENGTH(MESSAGE_LENGTH)) crc_calc (clk, reset, _tx.data[MESSAGE_LENGTH-1:0], crc_clear_r, crc_valid_r, crc_r, crc_ready_r);



task FSM();
    case (state)
        IDLE: begin
            _tx.ready <= uart.ready;
            segmentCount = 0;
            uart.valid <= 0;
            uart.data <= 0;
            crc_clear_r <= 0;
            if (_tx.valid) begin
                _tx.ready <= 0;
                crc_valid_r <= 1;
                state <= SEND_SEGMENT;
            end
        end
        SEND_SEGMENT: begin
            uart.data <= _tx.data[segmentCount*8 +: 8]; // From index segmentCount*8, take 8 bits
            uart.valid <= 1;
            if (!uart.ready) begin
                state <= AWAIT_SEGMENT_ACK;
            end
        end
        AWAIT_SEGMENT_ACK: begin
            crc_valid_r <= 0;
            uart.valid <= 0;
            if (uart.ready) begin
                segmentCount++;
                state <= CHECK_COUNT;
            end
        end
        CHECK_COUNT: begin
            if (segmentCount < SEGMENT_COUNT) begin
                state <= SEND_SEGMENT;
            end else begin
                state <= SEND_CRC;
            end
        end
        SEND_CRC: begin
            if (crc_ready_r) begin // Make sure CRC has been calculated and is ready to be sent
                uart.data <= crc_r;
                uart.valid <= 1;
                crc_clear_r <= 1;
                state <= AWAIT_CRC_ACK;
            end
        end
        AWAIT_CRC_ACK: begin
            uart.valid <= 0;
            if (uart.ready) begin
                state <= IDLE;
            end
        end
    endcase
endtask

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin 
        state <= IDLE;
        uart.valid <= 0;
        _tx.ready <= uart.ready;
        segmentCount = 0;
        crc_valid_r <= 0;
        crc_clear_r <= 0;
    end else begin
        FSM();
    end
end

assign _tx.sig = uart.sig;


//<statements>

endmodule
