/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

interface RegistersManagerInterface #(parameter                        
                            DATA_LENGTH = 32,
                            ADDRWIDTH = 8);
    
    logic                            writeAck;
    logic [DATA_LENGTH-1:0] 	     readData;

    logic [ADDRWIDTH - 1 : 0]        address;
    logic [DATA_LENGTH - 1 : 0]      writeData;
    logic                            writeEnable;
    logic 		   				     readEnable;
    logic                            writeAdmin;


modport internal (
    input  readData, writeAck,
    output address, writeData, writeEnable, readEnable, writeAdmin
);

modport external (
    output  readData, writeAck,
    input   address, writeData, writeEnable, readEnable, writeAdmin
);

endinterface //RegistersManagerInterface
