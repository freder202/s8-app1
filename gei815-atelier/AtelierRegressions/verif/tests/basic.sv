//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


  initial begin
    #200

	LogMessage(`NOTE, "Sending test uart strings");

	sendUartCommand (WRITE, COMMON, MASTER_ENABLE, `BIT_ENABLE);
	sendUartCommand (WRITE, COMMON, MASTER_ENABLE, `BIT_DISABLE);
	sendUartCommand (WRITE, COMMON, DEBUG_WAVE_OUTPUT, `BIT_ENABLE);

	sendUartCommand (WRITE, CHAN0, ANALOG_ENABLE, `BIT_ENABLE);
	sendUartCommand (WRITE, CHAN0, CHANNEL_ENABLE, `BIT_ENABLE);
	sendUartCommand (WRITE, CHAN0, DAC_OFFSET, 5);

	sendUartCommand (WRITE, CHAN1, ANALOG_ENABLE, `BIT_ENABLE);
	sendUartCommand (WRITE, CHAN1, SAMPLING_THRESHOLD, 12);
	sendUartCommand (WRITE, CHAN1, DAC_OFFSET, 14);
    #200
	$finish;
  end
