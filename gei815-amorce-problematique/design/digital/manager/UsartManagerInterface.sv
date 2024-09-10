/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

interface UsartManagerInterface
    #(parameter  
        MSG_LENGTH = 48,
        DATA_LENGTH = 32,
        ADDRWIDTH = 8,
        COMMAND_WIDTH = 5
    );
    // Registers declaration
    logic                            send_data;
    logic [MSG_LENGTH - 1:0]         tx_data;

    logic                            data_sent;
    logic                            packet_received;
    reg [COMMAND_WIDTH - 1: 0]       command;
    reg [ADDRWIDTH - 1: 0]           reg_addr;
    reg [DATA_LENGTH - 1: 0]         rx_data;

    
    modport internal(
        input  send_data, tx_data,
        output data_sent, packet_received, command, reg_addr, rx_data
    );

    modport external(
        output send_data, tx_data,
        input  data_sent, packet_received, command, reg_addr, rx_data
    );

    modport registersData(
        input reg_addr, rx_data
    );

    
endinterface // UsartManagerInterface