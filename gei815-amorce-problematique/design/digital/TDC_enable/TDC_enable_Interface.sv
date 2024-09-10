/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
package TDCEnablePackage;
endpackage

interface TDC_enable_Interface #(parameter
                            CHANNEL_COUNT = 2);
    logic [31:0]                        activate_channels;
    logic [CHANNEL_COUNT - 1:0]    enable_channels;
    logic                               channel_changed, read_ack, read_active_channel;

    modport internal (
        output enable_channels, read_active_channel,
        input  activate_channels, channel_changed, read_ack
    );

    modport external (
        input  enable_channels, read_active_channel,
        output activate_channels, channel_changed, read_ack
    );

    modport registersSignal (
    input read_active_channel,
    output activate_channels, read_ack
    );
endinterface //TDC_enable_Interface