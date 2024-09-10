/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

// Remove error from the width with the signals
/* verilator lint_off WIDTH */
`timescale 1ns/1ps


`ifndef IGNORE_USART_INCLUDE
    `include "UsartParam.svh"
`endif
module UsartTx
    // Parameters decleration
    #(parameter 
        LB_DATA_WIDTH   = $clog2(USART_DATA_LENGTH),
        CRC_LENGTH = 8,
        TRANSMISSION_LENGTH = USART_DATA_LENGTH + CRC_LENGTH)
    
    // Ports declaration
    (
     UsartInterface.tx                  _tx,
     input logic                        clk,
     input logic                        rsnt); 
    
    // States for the FSM
    typedef enum logic [2:0] {STATE_WAIT, STATE_CALCULATE_CRC, STATE_APPEND_CRC, STATE_LOAD, STATE_PARITY, STATE_END} states;

    states      state;

    // Registers. 
    logic [TRANSMISSION_LENGTH-1:0]     data_r;
    logic                       sig_r; // The bit to send
    logic                       ready_r;
    logic [LB_DATA_WIDTH-1:0]   data_cnt;
    logic                       parity_r;
    // This could be changed into an interface
    logic [CRC_LENGTH-1:0] crc_r;
    logic crc_valid_r;
    logic crc_clear_r;
    logic crc_ready_r;

    CRC8 #(.DATA_LENGTH(USART_DATA_LENGTH)) crc_calc (clk, !rsnt, _tx.data, crc_clear_r, crc_valid_r, crc_r, crc_ready_r);

    always_ff @( posedge clk ) begin
        if(!rsnt) begin
            state <= STATE_WAIT;
            sig_r <= 1;
            data_r <= 0;
            ready_r <= 1;
            data_cnt <= 0;
            crc_clear_r <= 0;
            crc_valid_r <= 0;
            parity_r <= USART_PARITY_MODE;
        end

        // Start the case if the 
        else begin
            
            case(state)

                // Wait for the DATA to enter
                STATE_WAIT : begin
                    if(!ready_r) begin
                        ready_r <= 1;
                    end
                    else if(_tx.valid) begin
                        state <= STATE_CALCULATE_CRC;
                        data_r [USART_DATA_LENGTH-1:0] <= _tx.data;
                        ready_r <= 0;
                        data_cnt <= 0;
                        parity_r <= USART_PARITY_MODE;
                    end
                end

                STATE_CALCULATE_CRC: begin
                    crc_valid_r <= 1;
                    state <= STATE_APPEND_CRC;
                end

                STATE_APPEND_CRC: begin
                    crc_valid_r <= 0;
                    if (crc_ready_r) begin
                        data_r [TRANSMISSION_LENGTH-1: TRANSMISSION_LENGTH-CRC_LENGTH] <= crc_r;
                        crc_clear_r <= 1;
                        sig_r <= 0;             // Start bit
                        state <= STATE_LOAD;
                    end
                end

                STATE_LOAD : begin
                    crc_clear_r <= 0;
                    sig_r <= data_r[data_cnt];
                    parity_r <= parity_r ^ data_r[data_cnt];

                    if(data_cnt == (TRANSMISSION_LENGTH  - 1)) begin
                        state <= STATE_PARITY;
                    end
                    else begin
                        data_cnt <= data_cnt + 1;
                        state <= STATE_LOAD;
                    end
                end

                STATE_PARITY : begin
                    state <= STATE_END;
                    sig_r <= parity_r;
                end

                STATE_END : begin
                    state <= STATE_WAIT;
                    sig_r <= 1;
                end

                default: begin
                    state <= STATE_WAIT;
                end
            endcase
        end
        
    end

    assign _tx.sig   = sig_r;
    assign _tx.ready = ready_r;


endmodule
