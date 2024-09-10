/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

interface SyncClkInterface #(parameter 
                            COUNTER_SIZE = 19);

logic                           resetCyclic;
logic                           clearError;
logic [COUNTER_SIZE - 1 : 0]    syncCounter;
logic                           errorFlag;

modport internal (
    input  resetCyclic, clearError,
    output syncCounter, errorFlag
);

modport external (
    output resetCyclic, clearError,
    input  syncCounter, errorFlag
);

modport registersSignal (
    input  errorFlag
);
    
endinterface //SyncClkInterface
