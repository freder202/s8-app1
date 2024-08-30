/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

import MessageWrapper::*;

module UsartManager
    #(parameter  
        MSG_LENGTH = 48,
        DATA_LENGTH = 32,
        ADDRWIDTH = 8,
        COMMAND_WIDTH = 5
    )
    // Ports
    (
    UsartManagerInterface.internal          _manager,
    UsartInterface.rx_reader                _rx_reader,
    UsartInterface.tx_writer                _tx_writer,
    input logic                             clk,
    input logic                             rsnt
    ) /* synthesis syn_noprune=1 */;
    
    // States for the differents status
    typedef enum logic [2:0] {STATE_WAIT, STATE_READ, STATE_SEND, STATE_SEND_NACK, STATE_END} states;

    states state;

    // Constant declaration 
    const logic [MSG_LENGTH - 1:0] c_Nack = 0;

    // '_r' means that the signal is assign to an output port
    // For rx output ports
    logic                            rx_ready_r;

    // For tx output ports
    reg [MSG_LENGTH - 1:0]           tx_data_r /* synthesis syn_preserve=1 syn_keep=1 alspreserve=1 */;
    logic                            tx_valid_r;
    
    // Output ports
    logic                            data_sent_r;
    logic                            packet_received_r;

    // local signals
    message_t                        message;

    //always @(state, _rx_reader.valid, _tx_writer.ready) begin//: FSM_Manager, MOORE
    task FSM();    
        case(state) 
            
            STATE_WAIT : begin
                if(_rx_reader.valid) begin
                    rx_ready_r = 1; // Told rx that we are reading his data
                    state = STATE_READ;
                end else if(_manager.send_data && _tx_writer.ready) begin
                    state = STATE_SEND;
                end
                data_sent_r = 0;
            end
            
            STATE_READ : begin
                rx_ready_r = 0; // Remove the flag reading data
                packet_received_r = 1;
                message.packet = _rx_reader.data;

                // Check if an error has occured
                state = _rx_reader.parity_error ? STATE_SEND_NACK : STATE_END;
            end

            STATE_SEND : begin
                tx_data_r = _manager.tx_data;
                tx_valid_r = 1;
                data_sent_r = 0;
                // Wait for transmission to start
                if (!_tx_writer.ready) begin
                    //tx_valid_r = 0;
                    data_sent_r = 1;
                    state = STATE_END; 
                end
            end
            
            // This will be something else in the future
            STATE_SEND_NACK : begin
                tx_valid_r = 1;
                tx_data_r = c_Nack;
                state = STATE_END;
            end

            STATE_END : begin
                //rx_ready_r = 0;
                packet_received_r = 0;
                tx_valid_r = 0;
                // Wait for tx to be ready before changing state (or we could read while tx not ready)
                if(_tx_writer.ready) begin
                    // Notify command manager that data_was sent
                    data_sent_r = 0;
                    state = STATE_WAIT;
                end
            end

            default: begin
                state = STATE_WAIT;
            end

        endcase 
    endtask

    always_ff @(posedge clk) begin //: Sync_reset
        if(!rsnt) begin
            state = STATE_WAIT;
            // Clear rx
            rx_ready_r = 0;
            // Clear tx signals
            tx_data_r = 0;
            tx_valid_r = 0;
            //Clear output ports
            data_sent_r = 0;
            packet_received_r = 0;
            message.packet = 0;
        end else begin
            FSM();
        end
    end

    // Map outputs with local variables
    assign _tx_writer.data  = tx_data_r;
    assign _tx_writer.valid = tx_valid_r;
    assign _rx_reader.ready = rx_ready_r;
    assign _manager.data_sent = data_sent_r;
    assign _manager.packet_received = packet_received_r;
    assign _manager.command = message.read.command;
    assign _manager.reg_addr = message.read.addr;
    assign _manager.rx_data = message.read.data;

endmodule
