//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind CRC8816 CRC8_Bindings
    #(.DATA_LENGTH(DATA_LENGTH),
    .DATA_LENGTH_BYTES(DATA_LENGTH_BYTES))

     inst_CRC8_Bindings(
        .cov_reset(reset),
        .cov_clk(clk),

        .cov_valid(i_valid),
        .cov_last(i_last),
        .cov_data(i_data),

        .cov_match(o_match),
        .cov_done(o_done),
        .cov_crc8(o_crc8)
	);

module CRC8_Bindings
    #(  
        DATA_LENGTH = 32,
        DATA_LENGTH_BYTES = DATA_LENGTH/8
    )
	(
        input logic cov_reset,
        input logic cov_clk,

        input logic cov_valid,
        input logic cov_last,
        input logic [7:0] cov_data,

        input logic cov_match,
        input logic cov_done,
        input logic [7:0] cov_crc8
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

string crc8_1_3_name = "CRC8.1.3: ";
//Assertion section
property p_reset;
    $rose(cov_reset) |=> ((cov_match == 0) && (cov_done == 0) && (8'h0D));
endproperty

ast_CRC8_reset : assert property(p_reset);
//cov_CRC8_reset : cover property(p_reset);



//Covergroup section
covergroup covg_CRC8
    @(posedge cov_clk);
    option.name = "cov_CRC8";
    reset : coverpoint cov_reset;
    valid : coverpoint cov_valid;
    i_last : coverpoint cov_last;
    i_data : coverpoint cov_data;
    o_match : coverpoint cov_match;
    o_done : coverpoint cov_done;
    o_crc8_0 : coverpoint cov_crc8[0];
    o_crc8_1 : coverpoint cov_crc8[1];
    o_crc8_2 : coverpoint cov_crc8[2];
    o_crc8_3 : coverpoint cov_crc8[3];
    o_crc8_4 : coverpoint cov_crc8[4];
    o_crc8_5 : coverpoint cov_crc8[5];
    o_crc8_6 : coverpoint cov_crc8[6];
    o_crc8_7 : coverpoint cov_crc8[7];
endgroup

covg_CRC8 cov_CRC8 = new();

//

endmodule