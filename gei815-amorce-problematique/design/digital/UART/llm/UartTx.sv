/*
    Author : Thomas Labb�
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

// Remove error from the width with the signals
/* verilator lint_off WIDTH */
`timescale 1ns/1ps
`ifndef UARTTX_DEF
`define UARTTX_DEF 1
`include "UartParam.svh"
`endif
module UartTx
    // Parameters decleration
    #(parameter 
        LB_DATA_WIDTH   = $clog2(UART_DATA_LENGTH),
        PULSE_WIDTH     = UART_CLK_FREQ / UART_BAUD_RATE, // Be sure that CLK_FREQ > BAUD_RATE
        LB_PULSE_WIDTH  = $clog2(PULSE_WIDTH),
        HALF_PULSE_WIDTH= PULSE_WIDTH/2)
    
    // Ports declaration
    (
     UartInterface.tx _tx,
     input logic                        clk,
     input logic                        reset); 
    
    // States for the FSM
    typedef enum logic [2:0] {STATE_WAIT, START_BIT, STATE_LOAD, STATE_PARITY, STATE_END} states;

    states      state;

    // Registers. 
    logic [UART_DATA_LENGTH-1:0]     data_r;
    logic                       sig_r; // The bit to send
    logic                       ready_r;
    logic [LB_DATA_WIDTH-1:0]   data_cnt;
    logic [LB_PULSE_WIDTH:0]    clk_cnt;
    logic                       parity_r;


    always_ff @( posedge clk ) begin
        if(!reset) begin
            state <= STATE_WAIT;
            sig_r <= 1;
            data_r <= 0;
            ready_r <= 0;
            data_cnt <= 0;
            clk_cnt <= 0;
            parity_r <= UART_PARITY_MODE;
        end

        // Start the case if the 
        else begin
            
            case(state)

                // Wait for the DATA to enter
                STATE_WAIT : begin
                    if(clk_cnt < PULSE_WIDTH[LB_PULSE_WIDTH:0]) begin
                        clk_cnt <= clk_cnt + 1;
                    end
                    else
                    if(!ready_r) begin
                        ready_r <= 1;
                    end
                    else if(_tx.valid) begin
                        state <= START_BIT;
                        sig_r <= 0;             // Start bit
                        data_r <= _tx.data;
                        ready_r <= 0;
                        data_cnt <= 0;
                        parity_r <= UART_PARITY_MODE;
                        clk_cnt <= 0;
                    end
                end
                
                START_BIT : begin
                    if(clk_cnt < PULSE_WIDTH[LB_PULSE_WIDTH:0]) begin
                        clk_cnt <= clk_cnt + 1;
                        sig_r <= 0;
                    end else begin
                    state <= STATE_LOAD;
                    clk_cnt <= 0;
                    end
                end

                STATE_LOAD : begin
                    if(clk_cnt < PULSE_WIDTH[LB_PULSE_WIDTH:0]) begin
                        clk_cnt <= clk_cnt + 1;
                        sig_r <= data_r[data_cnt];
                    end
                    else begin
                        parity_r <= parity_r ^ data_r[data_cnt];
                        clk_cnt <= 0;
                        if(data_cnt == (UART_DATA_LENGTH  - 1)) begin
                            state <= STATE_PARITY;
                        end
                        else begin
                            data_cnt <= data_cnt + 1; 
                        end
                    end
                    
                end

                STATE_PARITY : begin
                    if(clk_cnt < PULSE_WIDTH[LB_PULSE_WIDTH:0]) begin
                        clk_cnt <= clk_cnt + 1;
                        sig_r <= parity_r;
                    end else begin
                    state <= STATE_END;
                    
                    clk_cnt <= 0;
                    end
                end

                STATE_END : begin
                    if(clk_cnt < PULSE_WIDTH[LB_PULSE_WIDTH:0]) begin
                        clk_cnt <= clk_cnt + 1;
                        sig_r <= 1;
                    end
                    else begin
                    state <= STATE_WAIT;
                    clk_cnt <= 0;
                    end
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
