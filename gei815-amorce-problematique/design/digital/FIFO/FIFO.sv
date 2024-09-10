/*
    Author : Thomas Labb�
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
// Signal unoptimized ?
`timescale 1ns/1ps

import FIFOPackage::*;
/* verilator lint_off WIDTH */
module FIFO
    #(parameter 
        DATA_LENGTH = 16,
        DEPTH_LENGTH  = 16,
        DEPTH = $clog2(DEPTH_LENGTH))
        // Ports decleration
        (
            FIFOInterface.internal  bus,
            input logic             clk
        );
        
        // Registers
        reg [DATA_LENGTH - 1 : 0]             o_data_r;
        reg [DATA_LENGTH - 1 : 0]             memory[DEPTH_LENGTH];
        logic [DEPTH : 0]  fifo_cnt_write;
        logic [DEPTH : 0]  fifo_cnt_read;

        // Signals
        logic full_r;
        logic empty_r;
        logic full_error_r;
        logic empty_error_r;

        task write();
            if (full_r) begin
                full_error_r <= 1;
            end
            else begin
                memory[fifo_cnt_write[DEPTH - 1 : 0]] <= bus.i_data;
                fifo_cnt_write <= fifo_cnt_write + 1;
                full_error_r <= 0;
            end
        endtask

        task read();
            if (empty_r) begin
                empty_error_r <=1;
            end
            else  begin
                fifo_cnt_read <= fifo_cnt_read + 1;
                empty_error_r <= 0;
            end
        endtask
        

        
        always_ff @( posedge clk ) begin
            if (bus.clear) begin
                fifo_cnt_write <= 0;
                fifo_cnt_read <= 0;
                full_error_r <= 0;
                o_data_r <= 0;
            end
            else begin
                if (bus.write) begin
                    write();
                end
                if (bus.read) begin 
                    read();
                end   
            end
            o_data_r <= memory[fifo_cnt_read[DEPTH - 1 : 0]];
            full_r <= (fifo_cnt_write - fifo_cnt_read >= DEPTH_LENGTH);
            empty_r <= (fifo_cnt_read == fifo_cnt_write);
        end
        
        // Map the output with the local signals
        assign bus.full         = full_r;
        assign bus.empty        = empty_r;
        assign bus.full_error   = full_error_r;
        assign bus.empty_error  = empty_error_r;
        assign bus.o_data       = o_data_r;


endmodule
