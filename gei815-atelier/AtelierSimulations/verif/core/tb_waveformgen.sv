//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

`timescale 1ps/1ps

import cds_rnm_pkg::*;

// https://www.doulos.com/knowhow/sysverilog/tutorial/dpi/
// from https://community.cadence.com/cadence_blogs_8/b/fv/archive/2009/06/30/create-a-sine-wave-generator-using-systemverilog

import "DPI" pure function real sin (input real rTheta);
import "DPI" pure function real cos (input real rTheta);
import "DPI" pure function real log (input real rVal);
import "DPI" pure function real log10 (input real rVal);
import "DPI" pure function real exp (input real rVal);

//http://stackoverflow.com/questions/15034019/how-do-i-read-an-environment-variable-in-verilog-system-verilog
import "DPI-C" function string getenv(input string env_name);



module tb_waveformgen(output wrealsum waveform);

    gen_sinewave u_sinewave(waveform);
    gen_sawtooth u_sawtooth(waveform);

endmodule


module gen_sinewave(output wrealsum waveform);

    // Declarations
    parameter sampling_time = 100;
    bit sampling_clock = 0;
    bit gen_enable = 1'b0;

	parameter signalStep = 0.0039215;  // == 1/255;
    parameter pi = 3.141592;

	integer freq = 1_000_000; // in Hz
	integer iOffset = 128;
	integer iAmplitude = 120;
	integer iPhase = 0; //range is more or less pi
    real offset;
    real ampl;
	real phase;
    real sin_wave;

    always sampling_clock = #(sampling_time) ~sampling_clock;

    always @(sampling_clock) begin
        if(gen_enable == 1'b1) begin
			offset = iOffset    * signalStep;
			ampl   = iAmplitude * signalStep;
			phase  = iPhase/1000;
            sin_wave = offset + (ampl * sin(2*pi*freq*$time*1e-12 + phase)); // 1e-12 is to scale frequency to verilog timescale
        end else begin
            sin_wave = 0.0;
        end
    end

    assign waveform = sin_wave;

endmodule

module gen_sawtooth(output wrealsum waveform);

    // Declarations
    parameter sampling_time =100;
    bit sampling_clock = 0;
    bit gen_enable = 1'b0;

	parameter pi = 3.141592; // for identical phase parameter
	parameter signalStep = 0.0039215;  // == 1/255;

	integer freq = 1_000_000; // in Hz
	integer iOffset = 128;
	integer iAmplitude = 120;
	integer iPhase = 0; //range is more or less pi
	integer AdjustedTime;
    real offset;
    real ampl;
	real phase;
    real sawtooth_wave;
	integer period;


    always sampling_clock = #(sampling_time) ~sampling_clock;

    always @(sampling_clock) begin
        if(gen_enable == 1'b1) begin
			offset = iOffset    * signalStep;
			ampl   = iAmplitude * signalStep;
			period = 1e12 / freq;
			phase  = (iPhase*period)/(1000 * pi); // from rads to % in ps.
			AdjustedTime = $time;
			AdjustedTime = AdjustedTime + phase;


			// time is in ps. sawtooth will use period rather than frequency
            sawtooth_wave = offset + (ampl * (AdjustedTime % period))/period;
        end else begin
            sawtooth_wave = 0.0;
        end
    end

    assign waveform = sawtooth_wave;

endmodule
