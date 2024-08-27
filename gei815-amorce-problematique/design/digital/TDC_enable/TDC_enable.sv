/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

// Module used to activate the channels
`ifndef TDCENABLE_DEF
`define TDCENABLE_DEF 1
import TDCEnablePackage::*;
`endif

module TDC_enable #(parameter
                            CHANNEL_COUNT = 2)
    (// Ports declaration
        TDC_enable_Interface.internal           bus,
        input logic                             reset,
        input logic                             clk                      
    );

    // States
    typedef enum logic [0:0] {STATE_WAIT, STATE_READ_REG} states;
    states fsm_state;

    logic read_active_channel_r;
    logic [CHANNEL_COUNT - 1:0]     o_active_channel_r;
    
    always_ff @(posedge clk) begin
        if (reset) begin
            // Put all the outputs to 0
            fsm_state <= STATE_WAIT;
        end else begin
            case(fsm_state)
                STATE_WAIT : begin
                    if(bus.channel_changed == 1) begin
                        fsm_state <= STATE_READ_REG;
                    end
                end

                STATE_READ_REG : begin
                    read_active_channel_r <= 1;
                    if(bus.read_ack == 1) begin
                        fsm_state <= STATE_WAIT;
                        read_active_channel_r <= 0;
                        // activate_channels[16] is master switch. IF on, all channels enable.
                        o_active_channel_r = $left(bus.activate_channels) == 1 ? '1 : bus.activate_channels[CHANNEL_COUNT - 1:0];
                    end
                end
            endcase
        end
    end

    assign bus.enable_channels = o_active_channel_r;
    assign bus.read_active_channel = read_active_channel_r;

endmodule // TDC_enable
