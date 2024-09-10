/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

// This empty package is a workaround for Libero to include this file when necessary
package Threshold;
endpackage

interface ThresholdSetterInterface;
    logic [31:0]    threshold;
    logic           write, reset;

    // Use when the bus is set on the TDC module to output the events
    modport writer (
        output threshold, write, reset
    );

    // Use when the bus is set on an external module to read the events and enable the module
    modport reader (
        input threshold, write, reset
    );
endinterface //ThresholdSetterInterface