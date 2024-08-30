/*
    Author : Thomas Labb�
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/


// Libero instantiation of Interface, otherwise, it doesn't see the interfaces
`ifndef COMMANDMAN_DEF
`define COMMANDMAN_DEF 1
import EventsRatePackage::*;
import FIFOPackage::*;
import CommandManagerPackage::*;
`endif

import MessageWrapper::*;
import TDCTypes::TDC_CHANNEL;
import FIFOWrapper::*;

/* verilator lint_off WIDTH */
module CommandManager 
    #(parameter 
        FIFO_DATA_LENGTH = 68,
        MSG_LENGTH = 48,
        DATA_LENGTH = 32,
        COMMAND_WIDTH = 5,
        NUMBER_CHANNEL = 2
        )
    // Ports
    (
    CommandManagerInterface.internal        _manager,
    FIFOInterface.reader                    fifo,
    EventsRateInterface.external            _events_rate,
    input logic                             clk,
    input logic                             rsnt
    );
    
    // States of the different commands
    typedef enum logic [4:0] {STATE_INIT, STATE_WAIT, STATE_READ_EVENTS, STATE_WAIT_CONFIRMATION_EVENT, STATE_FIFO_READ, 
                              STATE_WAIT_FIFO_PROCESS, STATE_WRITE_REG, STATE_READ_REG, STATE_SEND_REG_VALUE, 
                              STATE_WAIT_CONFIRMATION, STATE_READ_EVENTS_RATE, STATE_SEND_EVENTS_RATE, 
                              STATE_SEND_ALL_EVENTS_RATE, STATE_WAIT_CONFIRMATION_ALL_EVENTS_RATE, 
                              STATE_RESET_EVENT_RATE} states;

    states state;

    // '_r' means that the signal (or reg) is assign to an output port
    // fifo output ports
    logic                           fifo_read_r;
    logic                           fifo_clear_r;

    // Output ports
    logic                           send_data_r;
    
    logic                           write_register_r;
    logic                           read_register_r;
    logic                           events_rate_read_r;

    // Local signals
    reg [5:0]                     msg_counter;
    logic                         command_received;

    message_t                     message;
    FIFO_t                        fifo_wrapper;

    // Initiate the message data
    initial begin
        message.write.data = 0;
    end

    assign fifo_clear_r = !rsnt;

    //always @(state, command_received, fifo.empty) begin // : FSM_Manager
    task FSM();  
        case(state) 
            STATE_INIT : begin
                state = STATE_WAIT;
                msg_counter = 0;
                command_received = 0;
                fifo_read_r = 0;
                send_data_r = 0;
                message.packet = 0;
                read_register_r = 0;
                write_register_r  = 0;
                events_rate_read_r = 0;
            end

            STATE_WAIT : begin
                // Reset the fifo_read_r and the send_data_flag
                fifo_read_r = 0;
                send_data_r = 0;
                if(command_received) begin
                    command_received = 0;
                    case (_manager.command)
                        read_register     : begin state = STATE_READ_REG; end
                        write_register    : begin state = STATE_WRITE_REG; end
                        read_events       : begin state = STATE_READ_EVENTS; end
                        read_events_rate  : begin state = STATE_READ_EVENTS_RATE; end
                        reset_events_rate : begin state = STATE_RESET_EVENT_RATE; end
                        default           : begin state = STATE_READ_EVENTS; end
                    endcase
                end else if(_events_rate.events_rate_ready) begin
                    events_rate_read_r = 1;
                    state = STATE_SEND_ALL_EVENTS_RATE;
                end
                else if(!fifo.empty) begin
                    state = STATE_READ_EVENTS;
                end
            end
            
            STATE_READ_EVENTS : begin
                fifo_wrapper.data = fifo.o_data;
                
                // Data type
                message.write.data_type = send_events;
                // Packet number
                message.write.packet_number = msg_counter;
                // Channel
                message.write.channel = fifo_wrapper.FIFO.channel;
                // Data to send (ToT and timestamp)
                message.write.data = msg_counter == 0 ? fifo_wrapper.FIFO.ToT : fifo_wrapper.FIFO.timestamp;

                send_data_r = 1;
                state = STATE_WAIT_CONFIRMATION_EVENT;

            end
            
            STATE_WAIT_CONFIRMATION_EVENT : begin
                // Wait for the confirmation that the data has been sent
                send_data_r = 0;
                if(_manager.data_sent) begin
                    if(msg_counter < 1) begin
                        state = STATE_READ_EVENTS;
                        msg_counter++;
                    end else begin
                        fifo_read_r = 1;
                        msg_counter = 0;
                        state = STATE_FIFO_READ;
                    end
                end
            end
            
            STATE_FIFO_READ: begin
                // Wait for two clock period before reading
                fifo_read_r = 0;
                state = STATE_WAIT_FIFO_PROCESS;
            end
            
            STATE_WAIT_FIFO_PROCESS: begin
                state = STATE_WAIT;
            end

            STATE_WRITE_REG : begin
                // Write inside the registers
                write_register_r = 1;
                if(_manager.write_register_ack) begin
                    write_register_r = 0;
                    
                    // Channel must set to default CHAN_0
                    message.write.channel = TDCTypes::CHAN_0;
                    message.write.packet_number = 0;
                    message.write.data = 0;
                    
                    // Data type
                    message.write.data_type = ack_write_reg;

                    send_data_r = 1;
                    state = STATE_WAIT_CONFIRMATION;
                end
            end

            STATE_READ_REG : begin
                read_register_r = 1;
                if (_manager.read_register_ack == 1) begin
                    read_register_r = 0;
                    state = STATE_SEND_REG_VALUE;
                end
            end

            STATE_SEND_REG_VALUE : begin
                // Channel must set to default CHAN_0
                message.write.channel = TDCTypes::CHAN_0;
                message.write.packet_number = 0;
                message.write.data = _manager.reg_data;
                // Data type
                message.write.data_type = read_reg;

                send_data_r = 1;
                state = STATE_WAIT_CONFIRMATION;
            end

            STATE_READ_EVENTS_RATE : begin
                //Give one clokc delay before sending the events_Rate
                state = STATE_SEND_EVENTS_RATE;
            end

            STATE_SEND_EVENTS_RATE : begin
                // Channel must not be null
                message.write.channel = TDC_CHANNEL'(_manager.rx_data[3:0]);
                message.write.packet_number = 0;
                // Data type
                message.write.data_type = events_count;
                
                // Should be sending event_counter for every channel 
                message.write.data = _events_rate.event_count[_manager.rx_data[3:0]];
                send_data_r = 1;
                state = STATE_WAIT_CONFIRMATION;
            end
            
            STATE_RESET_EVENT_RATE : begin
                events_rate_read_r = 1;
                // Data type
                message.write.data_type = ack_reset_events_rate;
                
                // Should be sending event_counter for every channel 
                message.write.data = 1;
                send_data_r = 1;
                state = STATE_WAIT_CONFIRMATION;
            end

            STATE_SEND_ALL_EVENTS_RATE : begin
                events_rate_read_r = 0;
                
                // Data type
                message.write.data_type = events_count;
                // Packet number
                message.write.packet_number = 0;
                // Channel
                message.write.channel = TDC_CHANNEL'(msg_counter[3:0]);
                // Events_count depending on the channels
                message.write.data = _events_rate.event_count[msg_counter[3:0]];

                send_data_r = 1;
                state = STATE_WAIT_CONFIRMATION_ALL_EVENTS_RATE;
            end

            STATE_WAIT_CONFIRMATION_ALL_EVENTS_RATE : begin
                // Wait for the confirmation that the data has been sent
                send_data_r = 0;
                if(_manager.data_sent) begin
                    if(msg_counter < NUMBER_CHANNEL - 1) begin
                        state = STATE_SEND_ALL_EVENTS_RATE;
                        msg_counter++;
                    end else begin
                        msg_counter = 0;
                        state = STATE_WAIT;
                    end
                end
            end

            STATE_WAIT_CONFIRMATION : begin
                events_rate_read_r = 0;
                // Wait for the confirmation that the data has been sent
                if(_manager.data_sent) begin
                    send_data_r = 0;
                    state = STATE_WAIT;
                end
            end
        
            default: begin
                state = STATE_WAIT;
            end

        endcase 
    endtask
 
    always_ff @(posedge clk) begin // Single process for all the task
        // State machine
        if(!rsnt) begin
            state = STATE_INIT;
        end 

        if (_manager.packet_received == 1) begin // If a packet_received, a new command is ready
            command_received = 1;
        end
        FSM();
    end

    assign fifo.read = fifo_read_r;
    assign fifo.clear = fifo_clear_r;
    assign _events_rate.read = events_rate_read_r;
    assign _manager.send_data = send_data_r;
    assign _manager.tx_data = message.packet;
    assign _manager.write_register = write_register_r;
    assign _manager.read_register = read_register_r;

endmodule
