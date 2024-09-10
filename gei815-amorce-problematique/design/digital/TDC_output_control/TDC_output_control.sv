/*
    Author : Thomas Labb�
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

// Module used to link TDC with mux
module TDC_output_control #(parameter
                            NUMBER_CHANNEL = 2,
                            DATA_LENGTH = 68)
    (// Ports declaration
        TDCInterface.external                   TDC1,
        TDCInterface.external                   TDC2,
        input logic                             reset,
        input logic                             clk,
        input logic                             fifo_full,
        output logic [DATA_LENGTH - 1:0]        o_data,
        output logic                            write,
        output logic [NUMBER_CHANNEL - 1 : 0]   sel_OneHot // For events rate
    );

    //logic [DATA_LENGTH - 1:0]                   o_data_r;
    logic [DATA_LENGTH - 1:0]                   data[NUMBER_CHANNEL];
    logic [NUMBER_CHANNEL - 1 : 0]              TDC_hasEvents;
    logic [NUMBER_CHANNEL - 1 : 0]              TDC_clear;
    logic [$clog2(NUMBER_CHANNEL) - 1 : 0]      sel_r;
    int i;

    //mux #(NUMBER_CHANNEL, DATA_LENGTH)
    //            mux_dut (.sel(sel_r), .i_data(data), .o_data(o_data_r));
    
    always_ff @(posedge clk) begin
        if (reset) begin
            // Put all the outputs to 0
            //for (int i=0; i<NUMBER_CHANNEL; i++) data[i] <= 0;
            data = '{default:0};
            sel_r = 0;
            TDC_clear = '{default:1};
            TDC_hasEvents = '{default:0};
            write = 0;
        end else begin
            TDC_clear = 0;
            write = 0;
            if(!fifo_full)begin
                
                // For each TDC, put the data in 68 bits
                // A more dynamic way ?
                data[0] = {TDC1.chan, TDC1.timeOverThreshold, TDC1.timestamp};
                data[1] = {TDC2.chan, TDC2.timeOverThreshold, TDC2.timestamp};
                
                // Selection of all the data
                TDC_hasEvents = {TDC2.hasEvent, TDC1.hasEvent};
                for (i=0; i < NUMBER_CHANNEL; i++) begin
                    if (TDC_hasEvents[i] == 1) begin
                        sel_r = i[$clog2(NUMBER_CHANNEL) - 1 : 0];
                        TDC_clear = 1 << i;
                        write = 1;
                        break;
                    end
                end
            end
        end
    end

    assign o_data = data[sel_r];
    assign sel_OneHot = reset == 0 ? TDC_clear : 0;
    assign {TDC2.clear, TDC1.clear} = TDC_clear;

endmodule // TDC_output_control
