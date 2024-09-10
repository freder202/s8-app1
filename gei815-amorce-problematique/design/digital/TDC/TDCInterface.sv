/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
package TDCTypes;
typedef enum bit[3:0]  {
    CHAN_0,
    CHAN_1,
    CHAN_2,
    CHAN_3,
    CHAN_4,
    CHAN_5,
    CHAN_6,
    CHAN_7,
    CHAN_8,
    CHAN_9, 
    CHAN_10,
    CHAN_11,
    CHAN_12,
    CHAN_13,
    CHAN_14,
    CHAN_15 
  } TDC_CHANNEL;
endpackage // TDCTypes

interface TDCInterface;
    logic [31:0]    timestamp, timeOverThreshold;
    TDCTypes::TDC_CHANNEL     chan;
    logic           hasEvent, clear;

    // Use when the bus is set on the TDC module to output the events
    modport internal (
        output timestamp, timeOverThreshold, chan, hasEvent,
        input clear
    );

    // Use when the bus is set on an external module to read the events and enable the module
    modport external (
        input timestamp, timeOverThreshold, chan, hasEvent,
        output clear
    );
endinterface //TDCInterface