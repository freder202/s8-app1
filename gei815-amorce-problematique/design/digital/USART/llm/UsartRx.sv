/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

`timescale 1ns/1ps


`ifndef IGNORE_USART_INCLUDE
    `include "UsartParam.svh"
`endif
module UsartRx 
    // Parameters decleration
    #(parameter 
        CRC_LENGTH = 8,
        TRANSMISSION_LENGTH = USART_DATA_LENGTH + CRC_LENGTH,
        LB_DATA_WIDTH   = $clog2(TRANSMISSION_LENGTH))
    
    // Ports declaration
     (UsartInterface.rx    _rx,
      input  logic         clk,
      input  logic         rsnt);

    // States for the FSM
    typedef enum logic [2:0] {STATE_WAIT, STATE_LOAD, STATE_PARITY, STATE_END, STATE_CALCULATE_CRC, STATE_AWAIT_CRC} states;
    states                   state;

    logic [TRANSMISSION_LENGTH-1:0]  data_tmp_r; // Put these data inside data_r when the reading is done
    logic [LB_DATA_WIDTH:0]  data_cnt;
    logic                    parity;
    logic                    crc_clear_r;
    logic                    crc_valid_r;
    logic [CRC_LENGTH-1:0]   crc_r;
    logic                    crc_ready_r;
    logic                    crc_match;

    //Output
    logic                    parity_error_r;
    logic [USART_DATA_LENGTH-1:0]  data_r;
    logic                    valid_r;

    CRC8 #(.DATA_LENGTH(USART_DATA_LENGTH)) crc_calc (clk, !rsnt, data_tmp_r[USART_DATA_LENGTH-1:0], crc_clear_r, crc_valid_r, crc_r, crc_ready_r);

   always_ff @(posedge clk) begin
        if (!rsnt) begin
            state <= STATE_WAIT;
            data_tmp_r <= 0;
            data_cnt <= 0;
            parity <= USART_PARITY_MODE;
            parity_error_r <= 0;
            crc_clear_r <= 0;
            crc_valid_r <= 0;
            crc_match <= 0;
        end
        else begin
            
            case(state)
            STATE_WAIT: begin
                crc_clear_r <= 0;
                crc_valid_r <= 0;
                crc_match <= 0;
                if(_rx.sig == 0) begin
                    data_cnt <= 0;
                    state    <= STATE_LOAD;
                end
            end

            // Recieve data and put it inside a temp value
            STATE_LOAD : begin
                data_tmp_r <= {_rx.sig, data_tmp_r[TRANSMISSION_LENGTH-1:1]};

                if (USART_PARITY_CHECK == 1) begin
                    parity <= parity ^ _rx.sig;
                end

                if(data_cnt >= TRANSMISSION_LENGTH - 1) begin
                    state <= STATE_PARITY;
                end
                else begin
                    data_cnt <= data_cnt + 1;
                end
            end


            STATE_PARITY: begin
                state <= STATE_END;
                parity_error_r <= (_rx.sig != parity && USART_PARITY_CHECK != 0);
                parity <= USART_PARITY_MODE;
            end

            // Wait for stop bit 
            STATE_END: begin
                if(_rx.sig) begin
                    state <= STATE_CALCULATE_CRC;
                end
            end

            STATE_CALCULATE_CRC: begin
                crc_valid_r <= 1;
                state <= STATE_AWAIT_CRC;
            end

            STATE_AWAIT_CRC: begin
                crc_valid_r <= 0;
                if (crc_ready_r) begin
                    // Do comparison
                    crc_match <= 1; //Fixme: current hardware implementation not working.
                    crc_clear_r <= 1;
                    state <= STATE_WAIT;
                end
            end

            default: begin
                state <= STATE_WAIT;
            end
            
            endcase
        end
       
   end

    // Outputs management
    always_ff @(posedge clk) begin
      if(!rsnt) begin
         data_r  <= 0;
         valid_r <= 0;
      end
      else if(crc_match && !valid_r) begin
         valid_r <= 1;
         data_r  <= data_tmp_r[USART_DATA_LENGTH-1:0];
      end
      else if(valid_r && _rx.ready) begin
         valid_r <= 0;
      end
   end

   assign _rx.data = data_r;
   assign _rx.valid = valid_r;
   assign _rx.parity_error = parity_error_r;
   
endmodule
