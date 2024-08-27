/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
import registers_sv_pkg::*;

module RegistersManager #(parameter
    DATA_LENGTH = 32,
    ADDRWIDTH = 8
) (
    CommandManagerInterface.registersData   _command,
    UsartManagerInterface.registersData     _usartMan,
    SyncClkInterface.registersSignal        _sync,
    TDC_enable_Interface.registersSignal    _TDC_en,
    RegistersManagerInterface.internal      _regMan,
    input  logic                            clk,
    input  logic                            rsnt                           
);

    // State for FSM
    typedef enum logic [3:0] {STATE_INIT, STATE_WAIT, STATE_WRITE_REG_COMMAND, STATE_WAIT_ACK_COMMAND,
                              STATE_WAIT_READ_REG_COMMAND, STATE_READ_REG_COMMAND, STATE_WRITE_ERROR_FLAG, STATE_WAIT_ACK,
                              STATE_WAIT_READ_CHAN_ENABLE, STATE_READ_ENABLE_CHANNELS} states;

    states state;

    // Local signals for outputs
    //Command
    logic                            writeAckCommand_r;
    logic                            readAckCommand_r;
    logic [DATA_LENGTH - 1 : 0]      reg_read_data_r;

    // Registers
    logic [ADDRWIDTH - 1 : 0]        address_r;
    logic [DATA_LENGTH - 1 : 0]      writeData_r;
    logic                            writeEnable_r;
    logic 		   				     readEnable_r;
    logic                            writeAdmin_r;

    //TDC_enable
    logic                            readChannel_r;

    // Initiate the message data
    initial begin
        // state = STATE_INIT;
    end

    always_ff @(posedge clk) begin // : Sync_reset
        if(!rsnt) begin
            state = STATE_INIT;
        end 
        FMS();
    end

    // Check the data to send in registers
    task FMS();    
        case(state)

            STATE_INIT : begin
                state = STATE_WAIT;
                writeAckCommand_r = 0;
                readAckCommand_r = 0;
                reg_read_data_r = 0;
                address_r = 0;
                writeData_r = 0;
                writeEnable_r = 0;
                readEnable_r = 0;
                writeAdmin_r = 0;
                readChannel_r = 0;
            end

            STATE_WAIT : begin
                // Put all the strobe to 0
                writeAckCommand_r = 0;
                readAckCommand_r = 0;
                readChannel_r = 0;

                if(_command.read_register == 1) begin
                    address_r = _usartMan.reg_addr;
                    // Start reading immediatly
                    // This is put here to start the reading two clocks before the commandManager gets it
                    readEnable_r = 1;
                    state = STATE_READ_REG_COMMAND;
                end else
                if (_command.write_register == 1) begin
                    state = STATE_WRITE_REG_COMMAND;
                end else
                if (_TDC_en.read_active_channel == 1) begin
                    address_r = 8;
                    readEnable_r = 1;
                    state = STATE_READ_ENABLE_CHANNELS;
                end else
                if (_sync.errorFlag == 1) begin
                    state = STATE_WRITE_ERROR_FLAG;
                end
            end

            STATE_WRITE_REG_COMMAND : begin
                address_r = _usartMan.reg_addr;
                writeData_r = _usartMan.rx_data;
                state = STATE_WAIT_ACK_COMMAND;
            end

            STATE_WAIT_ACK_COMMAND : begin
                writeEnable_r = 1;
                if(_regMan.writeAck) begin
                    writeEnable_r = 0;
                    writeAckCommand_r = 1;
                    state = STATE_WAIT;
                end
            end

            STATE_READ_REG_COMMAND : begin
                // Put the strobe to 0
                readEnable_r = 0;
                state = STATE_WAIT_READ_REG_COMMAND;
            end

            STATE_WAIT_READ_REG_COMMAND: begin
                reg_read_data_r = _regMan.readData;
                readAckCommand_r = 1;
                // Check if the command manager got the data value if not, stay in the same State
                if(_command.read_register == 0) begin
                    readAckCommand_r = 0;
                    state = STATE_WAIT;
                end else begin
                    state = STATE_WAIT_READ_REG_COMMAND;
                end
            end

            STATE_WRITE_ERROR_FLAG : begin
                address_r = FlagSyncError_addr[ADDRWIDTH - 1 :0];
                //Write strobe
                writeData_r = 1;
                state = STATE_WAIT_ACK;
            end

            STATE_WAIT_ACK : begin
                writeEnable_r = 1;
                writeAdmin_r = 1;
                if(_regMan.writeAck) begin
                    writeEnable_r = 0;
                    writeAdmin_r = 0;
                    state = STATE_WAIT;
                end
            end

            STATE_READ_ENABLE_CHANNELS : begin
                readEnable_r = 0;
                state = STATE_WAIT_READ_CHAN_ENABLE;
            end

            STATE_WAIT_READ_CHAN_ENABLE: begin
                _TDC_en.activate_channels = _regMan.readData;
                readChannel_r = 1;
                state = STATE_WAIT;
            end

            default : begin
                state = STATE_INIT;
            end

        endcase
    endtask
    
    // Assign output signals with local signals
    assign _command.write_register_ack = writeAckCommand_r;
    assign _command.read_register_ack = readAckCommand_r;
    assign _command.reg_data = reg_read_data_r;
    assign _regMan.address = address_r;
    assign _regMan.writeData = writeData_r;
    assign _regMan.writeEnable = writeEnable_r;
    assign _regMan.readEnable = readEnable_r;
    assign _regMan.writeAdmin = writeAdmin_r;
    assign _TDC_en.read_ack = readChannel_r;

endmodule