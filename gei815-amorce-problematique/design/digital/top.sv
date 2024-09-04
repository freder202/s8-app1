
/*
    Author(s) : Thomas Labbé, Gabriel Lessard
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ns/1ps
import TDCTypes::*;

/* verilator lint_off REDEFMACRO */
module top #(
    parameter
    MSG_LENGTH = 48,
    FIFO_DATA_LENGTH = 68,
    DEPTH_LENGTH = 16,
    DATA_LENGTH = 32,
    ADDRWIDTH = 8,
    COMMAND_WIDTH = 5,
    NUMBER_CHANNEL = 2,
    COUNTER_LENGTH = 32,
    NUMBER_BIT_CHANNEL = 1,
    TIMESTAMP_LENGTH = 32,
    USE_USART = 0,
    USE_TDC_DUMB = 1,
    USE_TDC_OSCILLATOR_CLOCK = 0
)(
    input logic clkMHz,
    input logic reset, clk, in_sig, resetCyclic,
   input logic [1:0] sipms,
    output logic out_sig, led, led2, led4, led9 
);  
    /***********************************/
    /********** Local signals **********/
    /***********************************/
    
    // Top
    logic                            led9_r;
    logic[32 :0]                     counter;
    
    //clk = clk_p and !clk_n;

    // TDC
    //logic [FIFO_DATA_LENGTH - 1 : 0] data_TDC[NUMBER_CHANNEL];
    logic [1 : 0]                    sel;
    logic [FIFO_DATA_LENGTH - 1 : 0] data_MUX;
    logic                            mux_available;
    logic [TIMESTAMP_LENGTH-1:0] timestamp;

    /***********************************/
    /************ Interfaces ***********/
    /***********************************/

    // Ports generation (Interfaces)    
    
    // Usart
    UsartInterface rx_if();
    UsartInterface tx_if();

    // FIFO
    FIFOInterface fifo_if();

    // TDC (for each channel)
    TDCInterface  tdc1_if();
    TDCInterface  tdc2_if();
    
    // UsartManager
    UsartManagerInterface usart_man_if();
    
    //CommandManager
    CommandManagerInterface #(MSG_LENGTH, DATA_LENGTH, COMMAND_WIDTH) command_if();

    // EventsRate
    EventsRateInterface #(COUNTER_LENGTH, NUMBER_CHANNEL) eventsrate_if();

    //Sync
    SyncClkInterface syncClk_if();

    //RegistersManager
    RegistersManagerInterface registers_man_if();

    //TDC_Enable
    TDC_enable_Interface #(NUMBER_CHANNEL) TDC_en_if();

    /***********************************/
    /************* Mapping *************/
    /***********************************/

    always_ff @( posedge clk ) begin
        if (reset) begin
            led9_r = 0;
            counter = 0;
        end;
        rx_if.sig = in_sig;
        eventsrate_if.clear = reset;
        syncClk_if.resetCyclic = resetCyclic;
        
        if(counter == 1000000) begin
            led9_r = !led9_r;
            counter = 0;
        end;

        counter++;
    end
    
    // Mapping USART with top
    //assign rx_if.sig = in_sig;
    assign out_sig = tx_if.sig;
    
    assign led = tx_if.sig;
    assign led2 = in_sig;
    assign led4 = resetCyclic;
    assign led9 = led9_r;

    // Map interface together (managers)
    assign usart_man_if.send_data = command_if.send_data;
    assign usart_man_if.tx_data = command_if.tx_data;
    assign command_if.data_sent = usart_man_if.data_sent;
    assign command_if.packet_received = usart_man_if.packet_received;
    assign command_if.command = usart_man_if.command;
    assign command_if.rx_data = usart_man_if.rx_data;

    packet_splitter inst_packet_splitter(tx_if.tx, clk, reset);
    packet_merger   inst_packet_merger(.message_if(rx_if.rx), .clk, .reset(reset));
   
    

    // FIFO mapping
    FIFO #(FIFO_DATA_LENGTH, DEPTH_LENGTH) 
                fifo_dut(.bus(fifo_if.internal), .clk);

    // Manager mapping
    UsartManager #(MSG_LENGTH, DATA_LENGTH, ADDRWIDTH, COMMAND_WIDTH)
                usartmanager_dut(._manager(usart_man_if.internal), ._rx_reader(rx_if.rx_reader), ._tx_writer(tx_if.tx_writer), .clk, .rsnt(!reset));

    CommandManager #(FIFO_DATA_LENGTH, MSG_LENGTH, DATA_LENGTH, COMMAND_WIDTH) 
                command_dut(._manager(command_if.internal), .fifo(fifo_if.reader), ._events_rate(eventsrate_if.external), .clk, .rsnt(!reset));

    RegistersManager registersmanager_dut(._command(command_if.registersData), ._usartMan(usart_man_if.registersData), ._sync(syncClk_if.registersSignal),
                                          ._regMan(registers_man_if.internal), ._TDC_en(TDC_en_if.registersSignal), .clk, .rsnt(!reset));

    // Registers
    Registers #(DATA_LENGTH, ADDRWIDTH)
                registers_dut(.address(registers_man_if.address), .writeEnable(registers_man_if.writeEnable), 
                              .writeData(registers_man_if.writeData), .readEnable(registers_man_if.readEnable), .clk,
                              .reset(reset), .readData(registers_man_if.readData), .writeAck(registers_man_if.writeAck),
                              .syncClearStrobe(syncClk_if.clearError), .writeAdmin(registers_man_if.writeAdmin),
                              .update_enable_channel(TDC_en_if.channel_changed));
    
    SyncClk SyncClk_dut(.bus(syncClk_if.internal), .clk(clk));

    /***************TDC***************/

    // TDC_output_control
    TDC_output_control #(NUMBER_CHANNEL, FIFO_DATA_LENGTH) 
                TDC_output_control_dut(.TDC1(tdc1_if.external), .TDC2(tdc2_if.external), .fifo_full(fifo_if.full),
                                       .clk(clk), .reset(reset), .o_data(fifo_if.i_data), .write(fifo_if.write),
                                       .sel_OneHot(eventsrate_if.enable));

    EventsRate # (COUNTER_LENGTH, NUMBER_CHANNEL)
                EventsRate_dut(.bus(eventsrate_if.internal), .clk);
    

    // TDC_dumb
    ThresholdSetterInterface thresholdSetter();
    assign thresholdSetter.reset = reset;
    Timestamp timestamp_module(resetCyclic, clk, timestamp);
    logic[1 :0]                     s_busy;


    TDC_dumb #(CHAN_0) inst_tdc_channel_0(
        .reset(reset),
        .clk(clk),
        .i_trigger(sipms[0]),
        .i_enable_channel(TDC_en_if.enable_channels[0]),
        .i_clear(tdc1_if.clear),
        .o_busy(s_busy[0]),
        .o_hasEvent(tdc1_if.hasEvent),
        .o_chanID(tdc1_if.chan),
        .o_timestamp(tdc1_if.timestamp),
        .o_pulseWidth(tdc1_if.timeOverThreshold)
    );
    TDC_dumb #(CHAN_1) inst_tdc_channel_1(
        .reset(reset),
        .clk(clk),
        .i_trigger(sipms[1]),
        .i_enable_channel(TDC_en_if.enable_channels[1]),
        .i_clear(tdc2_if.clear),
        .o_busy(s_busy[1]),
        .o_hasEvent(tdc2_if.hasEvent),
        .o_chanID(tdc2_if.chan),
        .o_timestamp(tdc2_if.timestamp),
        .o_pulseWidth(tdc2_if.timeOverThreshold)
    );

    // TDC_Enable
    TDC_enable #(NUMBER_CHANNEL) TDC_enable_dut(.bus(TDC_en_if.internal), .clk(clk), .reset);

endmodule
