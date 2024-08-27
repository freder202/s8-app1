//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

package randomGenClass;

typedef enum integer {SINWAVE = 1, SAWTOOTH = 2, IMPULSE_RESPONSE = 4, ALLOFF = 0} generatorType;


// Randomization example
// Constraints are realistic, but should be adapted to the target application
class CRandomChannelConfiguration;
	rand generatorType waveformType;
	rand integer waveAmplitude; // use integer instead of real
	rand integer waveOffset;
	rand integer wavePhase;
	rand integer dacOffset;
	rand integer triggerThreshold;


	rand logic [7:0] thresholdValue; // or randc
	rand logic [7:0] data;

	function void print();
		$display("Generated configuration is:");
		$display("    Waveform amplitude %d", waveAmplitude);
		$display("    Waveform offset    %d", waveOffset);
		$display("    Waveform phase     %d", wavePhase);
		$display("    Channel DAC        %d", dacOffset);
		$display("    Channel threshold  %d", triggerThreshold);
	endfunction

	constraint generatorSelection {
		waveformType == SINWAVE; // limit our example to the sinwave case
		//waveformType inside [SINWAVE, SAWTOOTH]; // limit our example to the sinwave case
	}

	// predefined range
	constraint waveAmplitudeMinMax {
		waveAmplitude <= 127; 	// max amplitude is 127 around center offset
		waveAmplitude > 4;		// wave has to change at least a bit
	}

	constraint waveOffsetMinMax {
		waveOffset <= 255;
		waveOffset >= 0;
	}

	// + or - pi * 1000, as defined in waveform gen implementation
	constraint wavePhaseMinMax {
		wavePhase <= 3141;
		wavePhase >= -3140;
	}

	constraint dacOffsetMinMax {
		dacOffset <= 255;
		dacOffset >= 0;
	}

	// keep scenarios within analog dynamic range
	constraint systemBoundaries {
		(waveOffset + waveAmplitude + dacOffset) <= 255;
		(waveOffset - waveAmplitude + dacOffset) >= 0;
	}

	// limits imposed by register resolution (8-bits)
	constraint triggerMinMax {
		triggerThreshold <= 255;
		triggerThreshold > 0;	// design cannot trigger with a value of 0
	}

	constraint placeTriggerInWaveform {
		triggerThreshold <= (waveOffset + waveAmplitude + dacOffset);
		triggerThreshold >  (waveOffset - waveAmplitude + dacOffset);
	}

endclass

endpackage
