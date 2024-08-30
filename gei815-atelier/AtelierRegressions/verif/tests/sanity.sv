//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


  initial begin

	fork MonitorUserFifoPort();
	join_none

	// wait for reset release
	@(negedge `DUT.reset)

	// wait for falling edge of clock
	@(negedge `DUT.clk)

	// Program channel 0 and channel 1 sources
	setWaveGenerator(0, SINWAVE,
						1_000_000, 	// frequency
						128, 		// amplitude
						128, 		// offset
						0);			// phase
	setWaveGenerator(1, SAWTOOTH,
						1_000_000, 	// frequency
						255, 		// amplitude
						0, 			// offset
						0);			// phase

	// Program channel 0 and 1
    configureChannel(CHAN0,			// channel
						  1, 	// chan enable
						  128,	// threshold
						  0,    // DAC value
						  4);	// sample offset

    configureChannel(CHAN1,			// channel
						  1, 	// chan enable
						  96,	// threshold
						  0,	// DAC value
						  7);	// sample offset

	MasterEnable(1);

	#20000


	///////////////////////////////////////////////////////////////////////////
	// Disable channel enable while master enable is active. Provoque error
	// for lab exercise.
	configureChannel(CHAN0,			// channel
						  0, 	// chan enable
						  0,	// threshold
						  0,    // DAC value
						  0);	// sample offset
	#2000
	//  -- end of code for assertion lab
	///////////////////////////////////////////////////////////////////////////





	// Do not erase beyond here
	EndOfSimulation();
  end
