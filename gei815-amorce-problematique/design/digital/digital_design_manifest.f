





$DESIGN_ROOT/digital/Registers/registers_sv_pkg.sv
$DESIGN_ROOT/digital/Registers/Registers.sv


$DESIGN_ROOT/digital/shared/mux.sv
$DESIGN_ROOT/digital/shared/counter.sv
$DESIGN_ROOT/digital/shared/DFF.sv
$DESIGN_ROOT/digital/shared/CRC8.sv
$DESIGN_ROOT/digital/shared/CRC8_gei816.sv


$DESIGN_ROOT/digital/UART/UartInterface.sv
$DESIGN_ROOT/digital/UART/llm/UartTx.sv
$DESIGN_ROOT/digital/UART/llm/UartRx.sv
$DESIGN_ROOT/digital/UART/packet_splitter.sv
$DESIGN_ROOT/digital/UART/packet_merger.sv

$DESIGN_ROOT/digital/USART/UsartInterface.sv
#$DESIGN_ROOT/digital/USART/UsartParam.svh
$DESIGN_ROOT/digital/USART/llm/UsartRx.sv

$DESIGN_ROOT/digital/TDC/TDCInterface.sv
$DESIGN_ROOT/digital/TDC_output_control/TDC_output_control.sv
//$DESIGN_ROOT/digital/TDC_dumb/TDC_dumb.sv
$DESIGN_ROOT/digital/TDC/ThresholdSetterInterface.sv
$DESIGN_ROOT/digital/TDC_enable/TDC_enable_Interface.sv
$DESIGN_ROOT/digital/TDC_enable/TDC_enable.sv
$DESIGN_ROOT/digital/TDC_calibration/pulse_generator.sv
$DESIGN_ROOT/digital/TDC/oscillator/DelayChain.sv
$DESIGN_ROOT/digital/TDC/oscillator/Oscillator.sv
$DESIGN_ROOT/digital/TDC/llm/Timestamp.sv

$DESIGN_ROOT/digital/FIFO/FIFOInterface.sv
$DESIGN_ROOT/digital/FIFO/FIFO.sv
$DESIGN_ROOT/digital/FIFO/FIFOWrapper.sv


$DESIGN_ROOT/digital/EventsRate/EventsRateInterface.sv
$DESIGN_ROOT/digital/EventsRate/EventsRate.sv
$DESIGN_ROOT/digital/SyncClkSystem/SyncClkInterface.sv
$DESIGN_ROOT/digital/SyncClkSystem/SyncClk.sv


$DESIGN_ROOT/digital/manager/MessageWrapper.sv
$DESIGN_ROOT/digital/manager/RegistersManagerInterface.sv
$DESIGN_ROOT/digital/manager/RegistersManager.sv
$DESIGN_ROOT/digital/manager/CommandManagerInterface.sv
$DESIGN_ROOT/digital/manager/CommandManager.sv
$DESIGN_ROOT/digital/manager/UsartManagerInterface.sv
$DESIGN_ROOT/digital/manager/UsartManager.sv

$DESIGN_ROOT/digital/top.sv


-incdir $DESIGN_ROOT/digital/Registers/
-incdir $DESIGN_ROOT/digital/USART/
-incdir $DESIGN_ROOT/digital/UART/
