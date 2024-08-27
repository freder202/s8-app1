/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
`timescale 1ns/1ps
package FIFOPackage;
endpackage

interface FIFOInterface
    #(parameter 
        LENGTH = 68,
        DEPTH_LENGTH  = 4);
    // Registers declaration
    reg   [LENGTH-1:0]    i_data;
    reg   [LENGTH-1:0]    o_data;

    logic                   write;
    logic                   read;
    logic                   clear;

    logic                   full;
    logic                   empty;

    logic                   full_error;
    logic                   empty_error;
    
    // Used inside the FIFO
    modport internal(
        input   i_data,
        input   write,
        input   read,
        input   clear,

        output  o_data,
        output  full,
        output  empty,
        output  full_error,
        output  empty_error
    );
    
    // For reading the FIFO
    modport reader(
        input   o_data,
        input   empty,
        input   empty_error,

        output  read,
        output  clear
    );

    // For writing in the FIFO
    modport writer(
        input   full,
        input   full_error,

        output  i_data,
        output  write,
        output  clear
    );
    
endinterface // FIFOInterface