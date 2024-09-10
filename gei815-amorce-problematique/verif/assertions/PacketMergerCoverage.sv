//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind packet_merger PacketMergerCoverage
    #(.DATA_LENGTH(DATA_LENGTH),
    .MESSAGE_LENGTH(MESSAGE_LENGTH),
    .CRC_LENGTH(CRC_LENGTH),
    .TRANSMISSION_LENGTH(TRANSMISSION_LENGTH),
    .SEGMENT_COUNT(SEGMENT_COUNT),
    .SEGMENT_COUNT_BITS(SEGMENT_COUNT_BITS))

     u_PacketMergerCoverage(
        .cov_reset(reset),
        .cov_clk(clk),

        .cov_messageValid(message_if.valid),
        .cov_messageReady(message_if.ready),
        .cov_messageData(message_if.data),

        .cov_uartReady(uart_if.ready),
        .cov_uartValid(uart_if.valid),
        .cov_uartData(uart_if.data),

        .cov_crcClear(crc_clear_r),
        .cov_crcValid(crc_valid_r),
        .cov_crcReady(crc_ready_r),
        .cov_crcAnswer(crc_r),

        .cov_segmentCount(segmentCount)
	);

module PacketMergerCoverage#(
    DATA_LENGTH = 8,
    MESSAGE_LENGTH = 48,
    CRC_LENGTH = 8,
    TRANSMISSION_LENGTH = MESSAGE_LENGTH+CRC_LENGTH,
    SEGMENT_COUNT = TRANSMISSION_LENGTH/DATA_LENGTH,
    SEGMENT_COUNT_BITS = $clog2(SEGMENT_COUNT)-1)
	(
	input logic cov_reset,
	input logic cov_clk,

    input logic cov_messageValid,
    input logic cov_messageReady,
    input logic [MESSAGE_LENGTH-1:0] cov_messageData,

    input logic cov_uartReady,
    input logic cov_uartValid,
    input logic [DATA_LENGTH-1:0] cov_uartData,

    input logic cov_crcClear,
    input logic cov_crcValid,
    input logic cov_crcReady,
    input logic [CRC_LENGTH-1:0] cov_crcAnswer,

    input logic [SEGMENT_COUNT_BITS:0] cov_segmentCount
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking





endmodule