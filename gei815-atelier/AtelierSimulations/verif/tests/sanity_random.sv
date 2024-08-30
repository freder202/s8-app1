//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


  initial begin

	static CRandomChannelConfiguration Configuration = new();

	fork MonitorUserFifoPort();
	join_none

    // wait for reset release
	@(negedge `DUT.reset)

	// wait for falling edge of clock
	@(negedge `DUT.clk)

	// do for channel 0
	if(Configuration.randomize() != 1)
		LogMessage(`WARNING, "Randomization error for channel 0. Review constraints");
	Configuration.print();
	setWaveGenerator(0, Configuration.waveformType,
							1_000_000,
							Configuration.waveAmplitude,
							Configuration.waveOffset,
							Configuration.wavePhase);

    configureChannel(CHAN0,			// channel
						  1, 	// chan enable
						  Configuration.triggerThreshold,
						  Configuration.dacOffset,
						  4);	// sample offset



	// do for channel 1
	if(Configuration.randomize() != 1)
		LogMessage(`WARNING, "Randomization error for channel 1. Review constraints");
	Configuration.print();
	setWaveGenerator(1, Configuration.waveformType,
							1_250_000,
							Configuration.waveAmplitude,
							Configuration.waveOffset,
							Configuration.wavePhase);
    configureChannel(CHAN1,			// channel
						  1, 	// chan enable
						  Configuration.triggerThreshold,
						  Configuration.dacOffset,
						  4);	// sample offset


	MasterEnable(1);

	#2000

	EndOfSimulation();
  end
