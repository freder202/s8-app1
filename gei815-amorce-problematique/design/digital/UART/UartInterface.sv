/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

interface UartInterface
    #(parameter 
        DATA_LENGTH = 48);
    // Registers declaration
    logic   [DATA_LENGTH-1:0] data;
    logic                     sig;
    logic                     valid;
    logic                     ready;
    logic                     parity_error;

    
    modport tx(input  data,
               input  valid,
               output sig,
               output ready);

    modport rx(output data,
               output valid,
               output parity_error,
               input  sig,
               input  ready);

    // Used for the UsartManager
    modport tx_writer(output data,
                      output valid,
                      input  ready);

    // Used for the UsartManager
    modport rx_reader(input  data,
                      input  valid,
                      input  parity_error,
                      output sig,
                      output ready);
    
endinterface // UsartInterface