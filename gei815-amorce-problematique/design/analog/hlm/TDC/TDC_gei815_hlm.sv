/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

`timescale 1ps/1ps

import TDCTypes::*;


// Randomization example
// Constraints are realistic, but should be adapted to the target application
class CRandomResolveTimes;
	rand integer RisingResolveTime;	// in Hz
	rand integer FallingResolveTime; // use integer instead of real

	function void print(int channel);
		$display("Generated Resolve times for channel %d are:", channel);
		$display("    RisingResolveTime %d ps", RisingResolveTime); // in MHz
		$display("    FallingResolveTime %d ps", FallingResolveTime);
	endfunction

	constraint RisingResolveTimeMinMax {
		RisingResolveTime <= 2_000_000; 	// Sampling at 100 MHz, so stay away from too fast cases
		RisingResolveTime >= 10_000;		// Not too slow so we do see something in short sim times
	}

	constraint FallingResolveTimeMinMax {
		FallingResolveTime <= 2_000_000; 	// Sampling at 100 MHz, so stay away from too fast cases
		FallingResolveTime >= 10_000;		// Not too slow so we do see something in short sim times
	}

endclass

localparam  TDC_RESOLVE_TIME = 2000000; // in picoseconds
localparam  TDC_DEAD_TIME = 200000; // in picoseconds

module TDC_dumb
    #(parameter
    TDC_CHANNEL channelNumber = CHAN_0
    )
    (// Ports declaration
        TDCInterface.internal bus,
        input                 clk,
        input                 reset,
        input                 trigger,
        input                 enable_channel,
        output                busy
    );

    // local variable
    CRandomResolveTimes ResolveTimes;
    reg find_falling_edge;
    reg got_falling_edge;
    reg set_output_values, r_set_output_values;
    reg deadtime_done ;
    reg saturate_time, r_saturate_time;
    reg r_busy;
    reg [31:0]    RisingTime, FallingTime;
    reg [31:0]    RisingResolveTime, FallingResolveTime;
    assign bus.chan = channelNumber;

    initial begin
        if(ResolveTimes == null)
	        ResolveTimes = new();

	    if(ResolveTimes == null)
	        $display("somethign is wrong, ResolveTimes is still null in channel %d.", channelNumber);
	    else
	        $display("ResolveTimes created for channel %d.", channelNumber);
	end


    always @(posedge trigger) begin

	    $display("Rising edge in channel %d.", channelNumber);
        if(!bus.hasEvent && !busy && enable_channel) begin
            RisingTime <= 32'($stime/40);

            if(ResolveTimes.randomize() != 1) begin
                $display("WARNING at %t, SV randomization error for TDC module %d", $time, channelNumber);
            end else begin
                ResolveTimes.print(channelNumber);
            end
        end
    end

    // save rising edge timing
    always @(negedge trigger && enable_channel) begin
        if(!bus.hasEvent && busy) begin
            FallingTime <= 32'($stime/40);
        end
    end


    // save falling edge timing
    always_ff @(posedge clk) begin
        find_falling_edge <= trigger;
        if (bus.clear || !enable_channel) begin
            got_falling_edge <= 0;
        end
        else if (busy) begin
            if(!trigger & find_falling_edge & !saturate_time) begin
                got_falling_edge <= 1;
            end
        end
    end


    // wait until resolve time for both to complete
    always_ff @(posedge clk) begin
        r_saturate_time <= saturate_time;
        if (bus.clear || !enable_channel) begin
            set_output_values <= 0;
        end
        else if (got_falling_edge & !saturate_time) begin
            if( ((RisingTime*40 + ResolveTimes.RisingResolveTime) < (32'($stime)))
              && ((FallingTime*40 + ResolveTimes.FallingResolveTime) < (32'($stime)))
              ) begin
                set_output_values <= 1;
            end
        end
        else if(saturate_time & !r_saturate_time) begin
            set_output_values <= 1;
        end
    end

    // set values to output and signal existing new data.
    always_ff @(posedge clk) begin
        r_set_output_values <= set_output_values;
        if (bus.clear || !enable_channel) begin
            bus.hasEvent <= 0;
        end
        else if (!r_set_output_values & set_output_values) begin
            bus.hasEvent <= 1;
            bus.timestamp <= RisingTime;
            if(!saturate_time) begin
                bus.timeOverThreshold <= FallingTime - RisingTime;
            end
            else begin
                bus.timeOverThreshold <= 5_000_000 / 40;
            end
        end
    end


    // wait for deadtime to complete
    always_ff @(posedge clk) begin
        if (!r_busy || reset || !enable_channel) begin
            deadtime_done <= 0;
        end
        else if (r_busy) begin
            if(saturate_time && (((RisingTime*40 + ResolveTimes.RisingResolveTime + 200000) < (32'($stime))))) begin
                deadtime_done <= 1;
            end
            else if(!saturate_time && ((RisingTime*40 + ResolveTimes.RisingResolveTime + 200000) < (32'($stime)))
              && ((FallingTime*40 + ResolveTimes.FallingResolveTime + 200000) < (32'($stime)))
              ) begin
                deadtime_done <= 1;
            end
        end
    end


    // busy goes 0 on clear, goes up on rising edge of trigger,
    always_ff @(posedge clk) begin
        if (deadtime_done || reset || !enable_channel) begin
            r_busy <= 0;
        end
        else if (!find_falling_edge & trigger) begin
            r_busy <= 1;
        end
    end

    assign busy = r_busy;


    // save falling edge timing
    always_ff @(posedge clk) begin
        if (deadtime_done || reset || !enable_channel || !busy) begin
            saturate_time <= 0;
        end
        else if (busy) begin
            if((RisingTime*40 + 5_000_000) < (32'($stime))) begin
                saturate_time <= 1;
            end
        end
    end

endmodule // TDC_dumb

