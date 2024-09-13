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
        input logic [DATA_LENGTH-1:0] cov_crc8
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

string crc8_1_3_name = "CRC8.1.3: ";
//Assertion section
property p_reset;
    $rose(cov_reset) |=> ((cov_match == 0) && (cov_done == 0) && (8'h0D));
endproperty

ast_reset : assert property(p_reset);
//cov_reset : cover property(p_reset);




string crc8_1_3_name = "CRC8.1.2: ";







string crc8_7_name "CRC8.7: o_crc8";




//Covergroup section

//

endmodule