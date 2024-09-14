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

//
//Assertion section
//

// CRC8.1.1	match devient 0.
// CRC8.1.2	done devient 0. 
// CRC8.1.3	o_crc8 devient 0x0D.
property p_reset;
    @(posedge cov_clk) $rose(cov_reset) |=> ((cov_match == 0) && (cov_done == 0) && (cov_crc8 == 8'h0D));
endproperty
ast_CRC8_1_1to3 : assert property(p_reset);

// CRC8.3.2	i_last toujours en même temps que valid
property p_last;
    @(posedge cov_clk) disable iff (cov_reset)
    $fell(cov_last) |-> $fell(cov_valid);
endproperty
ast_CRC8_3_2 : assert property(p_last);

// CRC8.5.1	o_done monte à ’1’ 1 à 2 coups d’horloge après last.
property p_done;
    @(posedge cov_clk) 
    ( $fell(cov_last) and !cov_reset ) |-> ( ##1 cov_done) or (##2 cov_done);
endproperty
ast_CRC8_5_1 : assert property(p_done);

// CRC8.5.2	o_done retombe à ’0’ seulement sur un reset.
property p_done_only_on_rst;
    @(posedge cov_clk)
    $fell(cov_done) |=> (cov_reset == 1);
endproperty
ast_CRC8_5_2 : assert property(p_done_only_on_rst);

// CRC8.6.2	o_match vaut ’1’ en même temps que done.
property p_crc8_6_2;
    @(posedge cov_clk) 
    $rose(cov_match) |-> (cov_done == 1);
endproperty
ast_CRC8_6_2 : assert property(p_crc8_6_2);

// CRC8.6.5	o_match Vaut ’0’ après un reset.
property p_crc8_6_5;
    @(posedge cov_clk)
    $fell(cov_reset) |=> (cov_match == 0)
endproperty
ast_CRC8_6_5 : assert property(p_crc8_6_5);

// CRC8.7.2 o_crc8 stable lorsque i_valid est à ’0’. 
property p_crc8_7_8;
    @(posedge cov_clk) disable iff (cov_reset)
    (!cov_valid) |-> ##1 (cov_crc8 == $past(cov_crc8,1));
endproperty
ast_CRC8_7_8 : assert property(p_crc8_7_8);

//
// Covergroup section
//

covergroup covg_CRC8
    @(posedge cov_clk);
    option.name = "cov_CRC8";

    //CRC8.2.1 Valid vu à ’1’ au moins une fois. 
    i_valid : coverpoint cov_valid iff (!cov_reset) {bins i_val[] = {1};}

    //CRC8.3.1 last vu à ’1’ au moins une fois
    i_last : coverpoint cov_last iff (!cov_reset) {bins i_last[] = {1};}

    //CRC8.4.1 Observé une variété des valeurs 8-bits
    i_data_full : coverpoint cov_data {bins poss_in_val[] = {[0:255]};}
    i_data_0 : coverpoint cov_data[0];
    i_data_1 : coverpoint cov_data[1];
    i_data_2 : coverpoint cov_data[2];
    i_data_3 : coverpoint cov_data[3];
    i_data_4 : coverpoint cov_data[4];
    i_data_5 : coverpoint cov_data[5];
    i_data_6 : coverpoint cov_data[6];
    i_data_7 : coverpoint cov_data[7];

    //CRC8.6.1 Observer que match passe par ses 2 états possibles lorsque done est ’1’. 
    o_done : coverpoint cov_done {bins poss_out_val[] = {1};}
    o_match : coverpoint cov_match;
    cross_done_match : cross o_done, o_match;

    //CRC8.7.1 Observé une variété des valeurs 8-bits 
    o_crc8_full : coverpoint cov_crc8 {bins poss_out_val[] = {[0:255]};}
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



/////////////OLD VERSION//////////////
//covergroup covg_CRC8
//    @(posedge cov_clk);
//    option.name = "cov_CRC8";
//    reset : coverpoint cov_reset;
//    valid : coverpoint cov_valid;
//    i_last : coverpoint cov_last;
//    i_data_full : coverpoint cov_data {bins poss_in_val[] = {[0:255]};}
//    i_data_0 : coverpoint cov_data[0]; // with {i_data_full && 1 };
//    i_data_1 : coverpoint cov_data[1]; // with {i_data_full >> 1 && 1 };
//    i_data_2 : coverpoint cov_data[2]; // with {i_data_full >> 2 && 1 };
//    i_data_3 : coverpoint cov_data[3]; // with {i_data_full >> 3 && 1 };
//    i_data_4 : coverpoint cov_data[4]; // with {i_data_full >> 4 && 1 };
//    i_data_5 : coverpoint cov_data[5]; // with {i_data_full >> 5 && 1 };
//    i_data_6 : coverpoint cov_data[6]; // with {i_data_full >> 6 && 1 };
//    i_data_7 : coverpoint cov_data[7]; // with {i_data_full >> 7 && 1 };
//    o_match : coverpoint cov_match;
//    o_done : coverpoint cov_done;
//    o_crc8_full : coverpoint cov_crc8 {bins poss_out_val[] = {[0:255]};}
//    o_crc8_0 : coverpoint cov_crc8[0]; // with {o_crc8_full && 1 };
//    o_crc8_1 : coverpoint cov_crc8[1]; // with {o_crc8_full >> 1 && 1 };
//    o_crc8_2 : coverpoint cov_crc8[2]; // with {o_crc8_full >> 2 && 1 };
//    o_crc8_3 : coverpoint cov_crc8[3]; // with {o_crc8_full >> 3 && 1 };
//    o_crc8_4 : coverpoint cov_crc8[4]; // with {o_crc8_full >> 4 && 1 };
//    o_crc8_5 : coverpoint cov_crc8[5]; // with {o_crc8_full >> 5 && 1 };
//    o_crc8_6 : coverpoint cov_crc8[6]; // with {o_crc8_full >> 6 && 1 };
//    o_crc8_7 : coverpoint cov_crc8[7]; // with {o_crc8_full >> 7 && 1 };
//endgroup
//covg_CRC8 cov_CRC8 = new();
//
//covergroup covg_i_data
//    @(posedge cov_clk);
//    option.name = "i_data";
//    // CRC8 4.1 Observé une variété des valeurs 8-bits
//    i_data_full : coverpoint cov_data {bins poss_in_val[] = {[0:255]};}
//    i_data_bit_0 : coverpoint cov_data[0]; // with {i_data_full && 1 };
//    i_data_bit_1 : coverpoint cov_data[1]; // with {i_data_full >> 1 && 1 };
//    i_data_bit_2 : coverpoint cov_data[2]; // with {i_data_full >> 2 && 1 };
//    i_data_bit_3 : coverpoint cov_data[3]; // with {i_data_full >> 3 && 1 };
//    i_data_bit_4 : coverpoint cov_data[4]; // with {i_data_full >> 4 && 1 };
//    i_data_bit_5 : coverpoint cov_data[5]; // with {i_data_full >> 5 && 1 };
//    i_data_bit_6 : coverpoint cov_data[6]; // with {i_data_full >> 6 && 1 };
//    i_data_bit_7 : coverpoint cov_data[7]; // with {i_data_full >> 7 && 1 };
//endgroup
//covg_i_data CRC8_4 = new();
//
//covergroup covg_o_done
//    @(posedge cov_clk);
//    option.name = "o_done";
//
//    o_done : coverpoint cov_done;
//
//    // CRC8 5.1	Monte à ’1’ 1 à 2 coups d’horloge après last.
//    // CRC8 5.2	Retombe à ’0’ seulement sur un reset.
//endgroup 
//covg_o_done CRC8_5 = new();
//
//covergroup covg_o_match
//    @(posedge cov_clk);
//    option.name = "o_match";
//
//    o_match : coverpoint o_match;
//
//    // CRC8 6.1	Monte à ’1’ 1 à 2 coups d’horloge après last.
//    // CRC8 6.2	Retombe à ’0’ seulement sur un reset.
//endgroup 
//covg_o_done CRC8_6 = new();
//
//covergroup covg_o_crc8
//    @(posedge cov_clk);
//    option.name = "o_CRC8";
//    // 7.1 Observé une variété des valeurs 8-bits 
//    o_crc8_full : coverpoint cov_crc8 {bins poss_out_val[] = {[0:255]};}
//    o_crc8_bit_0 : coverpoint cov_crc8[0]; // with {o_crc8_full && 1 };
//    o_crc8_bit_1 : coverpoint cov_crc8[1]; // with {o_crc8_full >> 1 && 1 };
//    o_crc8_bit_2 : coverpoint cov_crc8[2]; // with {o_crc8_full >> 2 && 1 };
//    o_crc8_bit_3 : coverpoint cov_crc8[3]; // with {o_crc8_full >> 3 && 1 };
//    o_crc8_bit_4 : coverpoint cov_crc8[4]; // with {o_crc8_full >> 4 && 1 };
//    o_crc8_bit_5 : coverpoint cov_crc8[5]; // with {o_crc8_full >> 5 && 1 };
//    o_crc8_bit_6 : coverpoint cov_crc8[6]; // with {o_crc8_full >> 6 && 1 };
//    o_crc8_bit_7 : coverpoint cov_crc8[7]; // with {o_crc8_full >> 7 && 1 };
//    // 7.2
//endgroup
//covg_o_crc8 CRC8_7 = new();
//
//


endmodule
