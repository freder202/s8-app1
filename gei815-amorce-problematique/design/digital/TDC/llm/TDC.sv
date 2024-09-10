/*
    Author : Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`ifndef TDC_DEF
`define TDC_DEF 1
import TDCTypes::*;
import Threshold::*;
`endif

module TDC
    #(parameter 
        TDC_CHANNEL channelNumber = CHAN_0,
        int USE_QUAD_OSCILLATOR = 0
    )
    (// Ports:
        TDCInterface.internal bus,
        ThresholdSetterInterface.reader setter,
        input clk,
        input logic sipm,
        input logic enable,
        input logic [31:0] timestamp
    );

   
    // Registers
    logic r_counting, r_hasEvent, r_writeThreshold, r_timeOverThresholdReady;
    logic [31:0] r_timeOverThreshold, r_timestamp;

    // Modules
    OverThreshold ovt(.setter(setter), .signal(r_timeOverThreshold), .detect(r_hasEvent)); 
    // DFF hasEventFlipFlop(.clk(r_timeOverThresholdReady), .D(r_hasEvent), .rst(bus.clear), .Q(bus.hasEvent));
    generate
        // Uses the method with four dephased clocked instead of a delay chain
        if (USE_QUAD_OSCILLATOR) begin
            OscillatorQuadrature oscillatorClk(.enable(r_counting), .clk(clk), .reset(bus.clear), .count(r_timeOverThreshold), .hasValue(r_timeOverThresholdReady));
        end
        else begin
            Oscillator oscillator(.enable(r_counting), .reset(bus.clear), .count(r_timeOverThreshold), .hasValue(r_timeOverThresholdReady));
        end
    endgenerate
    
    
    assign bus.chan = channelNumber;
    assign r_counting = sipm && !bus.hasEvent && enable;
    
    always_ff @(posedge r_counting) begin 
        // Start and stop the counter
        r_timestamp <= timestamp;
    end

    // Set values on bus
    always_ff @( posedge r_timeOverThresholdReady or posedge bus.clear) begin
        if (bus.clear) begin
            bus.hasEvent <= 0;
        end 
        else begin
            bus.timestamp <= r_timestamp;
            bus.hasEvent <= r_hasEvent;
            bus.timeOverThreshold <= r_timeOverThreshold;    
        end
    end
endmodule // TDC