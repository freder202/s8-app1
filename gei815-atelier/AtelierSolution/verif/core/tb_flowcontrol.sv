//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps


`define DUT             tb_top.u_dut
`define GENERATOR_CHAN0 tb_top.u_waveformgen0
`define GENERATOR_CHAN1 tb_top.u_waveformgen1
`define UART_CLOCK 		tb_top.clk

`define ERROR			2
`define WARNING			1
`define NOTE			0

`define BIT_ENABLE		1
`define BIT_DISABLE		0

import randomGenClass::CRandomChannelConfiguration;

typedef enum integer {SINWAVE = 1, SAWTOOTH = 2, IMPULSE_RESPONSE = 4, ALLOFF = 0} generatorType;
typedef enum integer {READ = 0, WRITE = 1} uart_mode;
typedef enum integer {CHAN0 = 0, CHAN1 = 1, COMMON = 2} treg_bank;
typedef enum integer {MASTER_ENABLE = 0,
					  DEBUG_WAVE_OUTPUT = 1
					  } registersCommon;
typedef enum integer {CHANNEL_ENABLE = 0,
					  ANALOG_ENABLE = 1,
					  SAMPLING_THRESHOLD = 2,
					  DAC_OFFSET = 3,
					  SAMPLE_OFFSET = 4
					  } registersChannel;

// Flow control module declaration
// contains the task library and the test's include statement at the end.
module tb_flowcontrol(input clk,
					 output reg uart_in,
					 input uart_out,
					 output reg userif_SampleRead,
					 input userif_SampleEmpty,
					 input [15:0] userif_SampleData);

	// Message helper items and initialization
	integer ErrorMessages = 0;
	integer WarningMessages = 0;
	initial $timeformat(-9, 6, " ns", 10);
	initial $printtimescale;


	// output initialization
	initial uart_in = 1;
	initial userif_SampleRead = 0;

	// Logging helper function
	task LogMessage(input integer Type, input string message);
		string MessageHeader;
		if(Type == `ERROR)
		begin
			ErrorMessages++;
			MessageHeader = "ERROR";
		end
		else if(Type == `WARNING)
		begin
			WarningMessages++;
			MessageHeader = "WARNING";
		end
		else
			MessageHeader = "NOTE";

		$display("%s At %t : %s", MessageHeader, $time, message);
	endtask

	// Prints end of simulation messages and actual simulation termination
	task EndOfSimulation();

		$display("End of test. Summary:");
		if(ErrorMessages != 0)
			$display("%d ERRORS", ErrorMessages);
		else
			$display("No bench errors!");

		if(WarningMessages != 0)
			$display("%d WARNINGS", WarningMessages);

		$finish;
	endtask

	// Sends out register read/write requests through the UART port.
	task sendUartCommand (input uart_mode mode, input treg_bank reg_bank, input integer addr, input integer data);

		bit [15:0] Packet;
		integer unsigned CastPacket;

		// Format following the spec
		Packet[15:14] = mode;		// read/write
		Packet[13:12] = reg_bank;	// register bank
		Packet[11:8] = addr;		// register index
		Packet[7:0] = data;			// value

		CastPacket = Packet;
		$display("Sending string %04x", CastPacket);

		// Create stop bit
		@(negedge `UART_CLOCK);
		uart_in = 0;

		// send 16 bits
		for(int i = 0; i < 16; i++) begin
			@(negedge `UART_CLOCK);
			uart_in = Packet[i];
		end

		// send parity (if wanted). After send stop bit
		@(negedge `UART_CLOCK);
		uart_in = 1; // only stop bit for now
	endtask

	// uses force/release commands. Will be better modeled with class in Object Oriented test bench
	// use these calls with care.
	task setSinWaveParameters(input unsigned channel,
							  input integer frequency,
							  input integer amplitude,
							  input integer offset,
							  input integer phase
							  );
		if(channel == 0)
		begin
			force `GENERATOR_CHAN0.u_sinewave.freq       = frequency;
			force `GENERATOR_CHAN0.u_sinewave.iOffset    = offset;
			force `GENERATOR_CHAN0.u_sinewave.iAmplitude = amplitude;
			force `GENERATOR_CHAN0.u_sinewave.iPhase     = phase;
			release `GENERATOR_CHAN0.u_sinewave.freq;
			release `GENERATOR_CHAN0.u_sinewave.iOffset;
			release `GENERATOR_CHAN0.u_sinewave.iAmplitude;
			release `GENERATOR_CHAN0.u_sinewave.iPhase;
		end
		else if(channel == 1)
		begin
			force `GENERATOR_CHAN1.u_sinewave.freq       = frequency;
			force `GENERATOR_CHAN1.u_sinewave.iOffset    = offset;
			force `GENERATOR_CHAN1.u_sinewave.iAmplitude = amplitude;
			force `GENERATOR_CHAN1.u_sinewave.iPhase     = phase;
			release `GENERATOR_CHAN1.u_sinewave.freq;
			release `GENERATOR_CHAN1.u_sinewave.iOffset;
			release `GENERATOR_CHAN1.u_sinewave.iAmplitude;
			release `GENERATOR_CHAN1.u_sinewave.iPhase;
		end
	endtask
	task setSawWaveParameters(input unsigned channel,
							  input integer frequency,
							  input integer amplitude,
							  input integer offset,
							  input integer phase
							  );
		if(channel == 0)
		begin
			force `GENERATOR_CHAN0.u_sawtooth.freq       = frequency;
			force `GENERATOR_CHAN0.u_sawtooth.iOffset    = offset;
			force `GENERATOR_CHAN0.u_sawtooth.iAmplitude = amplitude;
			force `GENERATOR_CHAN0.u_sawtooth.iPhase     = phase;
			release `GENERATOR_CHAN0.u_sawtooth.freq;
			release `GENERATOR_CHAN0.u_sawtooth.iOffset;
			release `GENERATOR_CHAN0.u_sawtooth.iAmplitude;
			release `GENERATOR_CHAN0.u_sawtooth.iPhase;
		end
		else if(channel == 1)
		begin
			force `GENERATOR_CHAN1.u_sawtooth.freq       = frequency;
			force `GENERATOR_CHAN1.u_sawtooth.iOffset    = offset;
			force `GENERATOR_CHAN1.u_sawtooth.iAmplitude = amplitude;
			force `GENERATOR_CHAN1.u_sawtooth.iPhase     = phase;
			release `GENERATOR_CHAN1.u_sawtooth.freq;
			release `GENERATOR_CHAN1.u_sawtooth.iOffset;
			release `GENERATOR_CHAN1.u_sawtooth.iAmplitude;
			release `GENERATOR_CHAN1.u_sawtooth.iPhase;
		end
	endtask

	// select which wave type to show the analog port
	// Shows how to use the force statement. Not recommended for
	// modifying values in the design, except for error tolerance tests.
    task setWaveGenerator (input unsigned channel,
						   input generatorType sourceMask,
						   input integer frequency,
						   input integer amplitude,
						   input integer offset,
						   input integer phase);

		if(channel == 0)
		begin
			if (sourceMask == SINWAVE) begin
				force `GENERATOR_CHAN0.u_sinewave.gen_enable = 1'b1;
				setSinWaveParameters(channel, frequency, amplitude, offset, phase);
			end else
				force `GENERATOR_CHAN0.u_sinewave.gen_enable = 1'b0;


			if (sourceMask == SAWTOOTH) begin
				force   `GENERATOR_CHAN0.u_sawtooth.gen_enable = 1'b1;
				setSawWaveParameters(channel, frequency, amplitude, offset, phase);
			end else
				force   `GENERATOR_CHAN0.u_sawtooth.gen_enable = 1'b0;
		end
		else if(channel == 1)
		begin
			if (sourceMask == SINWAVE)  begin
				force `GENERATOR_CHAN1.u_sinewave.gen_enable = 1'b1;
				setSinWaveParameters(channel, frequency, amplitude, offset, phase);
			end else
				force `GENERATOR_CHAN1.u_sinewave.gen_enable = 1'b0;


			if (sourceMask == SAWTOOTH)  begin
				force   `GENERATOR_CHAN1.u_sawtooth.gen_enable = 1'b1;
				setSawWaveParameters(channel, frequency, amplitude, offset, phase);
			end else
				force   `GENERATOR_CHAN1.u_sawtooth.gen_enable = 1'b0;
		end

		if(channel < 2)
			$display("Using %s generator in channel %d", sourceMask.name(), channel);
		else
			$display("Unsupported channel", sourceMask.name(), channel);

    endtask

	// send channel register configurations
    task configureChannel(input treg_bank channelId,
						  input integer channelEnable,
						  input integer threshold,
						  input integer dacValue,
						  input integer sampleOffset);

		//----------------------------------------------------------------------
		// For lab 4.1.2, fix analog sequencing assertion.
		// Analog enable is not changed at all until the comments are removed,
		// causing an assertion error. This first section here raises the analog 
		// enable before the digital enable. Next commented block will clear 
		// the analog enable _after_ the digital enable.
		//
		if(channelEnable == 1)
    		sendUartCommand(WRITE, channelId, ANALOG_ENABLE, channelEnable);
		//----------------------------------------------------------------------


		// Register write sequence
		sendUartCommand(WRITE, channelId, CHANNEL_ENABLE, channelEnable);
		sendUartCommand(WRITE, channelId, SAMPLING_THRESHOLD, threshold);
		sendUartCommand(WRITE, channelId, DAC_OFFSET, dacValue);
		sendUartCommand(WRITE, channelId, SAMPLE_OFFSET, sampleOffset);


		//----------------------------------------------------------------------
		// For lab 4.1.2, fix analog sequencing assertion.
		// Analog enable is not changed at all until the comments are removed,
		// causing an assertion error. This second section clears 
		// the analog enable _after_ the digital is disabled.
		//
		if(channelEnable == 0)
    		sendUartCommand(WRITE, channelId, ANALOG_ENABLE, channelEnable);
		//----------------------------------------------------------------------

	endtask

	// Task dedicated to the master enable, to ease reading the code
	task MasterEnable(input integer setting);
		sendUartCommand(WRITE, COMMON, 0, setting);
	endtask

	// Monitor function that reads out the user fifo interface
	// when data is available. Prints the 16-bit words without
	// checking them.
	task MonitorUserFifoPort();
		forever begin
			@(posedge clk)

			// if not empty
			if(userif_SampleEmpty == 1'b0) begin

				// print 16-bit word fully and by segment
				$display("@%t : On fifo port, data 0x%4x  :: %x %x %02x",
					$time, userif_SampleData,
					userif_SampleData[15:12],
					userif_SampleData[11:8],
					userif_SampleData[7:0] );
				// toggle fifo read bit
				userif_SampleRead = 1'b1;
			end
			else begin
				userif_SampleRead = 1'b0;
			end
		end
	endtask






    // include test from symbolic link source
    `include "current_test.sv"

endmodule
