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

//Assertion section
property p_reset;
    @(posedge cov_clk) $rose(cov_reset) |=> ((cov_match == 0) && (cov_done == 0) && (cov_crc8 == 8'h0D));
endproperty

ast_CRC8_reset : assert property(p_reset);
//cov_CRC8_reset : cover property(p_reset);

property p_last;
    @(posedge cov_clk) disable iff (cov_reset)
    $rose(cov_last) |-> cov_valid;
endproperty
ast_CRC8_last : assert property(p_last);

property p_done;
    @(posedge cov_clk) disable iff (cov_reset)
    $fell(cov_last) |-> ##2 cov_done;
endproperty
ast_CRC8_done : assert property(p_done);

property p_done_only_on_rst;
    @(posedge cov_clk) disable iff (cov_reset)
    $fell(cov_done) |=> (cov_reset == 1);
endproperty
ast_done_only_on_rst : assert property(p_done_only_on_rst);



//Covergroup section
covergroup covg_CRC8
    @(posedge cov_clk);
    option.name = "cov_CRC8";
    reset : coverpoint cov_reset;
    valid : coverpoint cov_valid;
    i_last : coverpoint cov_last;
    i_data_full : coverpoint cov_data {bins poss_in_val[] = {[0:255]};}
    i_data_0 : coverpoint cov_data[0];
    i_data_1 : coverpoint cov_data[1];
    i_data_2 : coverpoint cov_data[2];
    i_data_3 : coverpoint cov_data[3];
    i_data_4 : coverpoint cov_data[4];
    i_data_5 : coverpoint cov_data[5];
    i_data_6 : coverpoint cov_data[6];
    i_data_7 : coverpoint cov_data[7];
    o_match : coverpoint cov_match;
    o_done : coverpoint cov_done;
    o_crc8_full : coverpoint cov_crc8 {bins poss_out_val[] = {[0:255]};}
    o_crc8_0 : coverpoint cov_crc8[0] with { i_data_full && 1 };
    o_crc8_1 : coverpoint cov_crc8[1] with { i_data_full >> 1 && 1 };
    o_crc8_2 : coverpoint cov_crc8[2] with { i_data_full >> 2 && 1 };
    o_crc8_3 : coverpoint cov_crc8[3] with { i_data_full >> 3 && 1 };
    o_crc8_4 : coverpoint cov_crc8[4] with { i_data_full >> 4 && 1 };
    o_crc8_5 : coverpoint cov_crc8[5] with { i_data_full >> 5 && 1 };
    o_crc8_6 : coverpoint cov_crc8[6] with { i_data_full >> 6 && 1 };
    o_crc8_7 : coverpoint cov_crc8[7] with { i_data_full >> 7 && 1 };
endgroup



covg_CRC8 cov_CRC8 = new();

//

endmodule