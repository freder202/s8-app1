/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ns/1ps
package EventsRatePackage;
endpackage

interface EventsRateInterface
    #(parameter 
        COUNTER_LENGTH = 24,
        CHANNEL_NUMBER = 2);
    // Registers declaration
    reg   [COUNTER_LENGTH-1:0]  event_count[CHANNEL_NUMBER];

    reg   [CHANNEL_NUMBER-1:0]  enable;
    logic                       read;
    logic                       clear;
    logic                       events_rate_ready;
    
    modport internal(
        input   enable, read, clear,
        output  events_rate_ready, event_count
    );
    
    modport external(
        input   events_rate_ready, event_count,
        output  enable, read, clear
    );
    
endinterface // EventsRateInterface