/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
package CommandManagerPackage;
endpackage

interface CommandManagerInterface
    #(parameter 
        MSG_LENGTH = 48,
        DATA_LENGTH = 32,
        COMMAND_WIDTH = 5
        );
    // Registers declaration
    logic                           data_sent;
    logic                           packet_received;
    logic [COMMAND_WIDTH - 1 : 0]   command;
    logic                           write_register_ack;
    reg [DATA_LENGTH - 1 : 0]       reg_data;
    reg [DATA_LENGTH - 1 : 0]       rx_data;

    logic                           send_data;
    logic [MSG_LENGTH - 1:0]        tx_data;
    logic                           write_register;
    logic                           read_register;
    logic                           read_register_ack;

    
    modport internal(
        input  data_sent, packet_received, command, write_register_ack, reg_data, rx_data, read_register_ack,
        output send_data, tx_data, write_register, read_register
    );

    modport external(
        output  data_sent, packet_received, command, write_register_ack, reg_data, rx_data, read_register_ack,
        input   send_data, tx_data, write_register, read_register
    );

    modport registersData(
        output write_register_ack, reg_data, read_register_ack,
        input write_register, read_register
    );

    
endinterface // CommandManagerInterface