//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


// Bind statement usage in mixed-langage environments
//			https://www.youtube.com/watch?v=VuBqJoTRYyU


bind Registers RegisterBankCoverage u_RegisterBankCoverage(
	.cov_reset(reset),
	.cov_clk(clk),
	.cov_writeEnable(writeEnable),
	.cov_writeAck(writeAck),
	.cov_readEnable(readEnable),
	.cov_address(address)
	);

module RegisterBankCoverage
	//#(parameter g_ChannelId = 15)
	(
	input logic cov_reset,
	input logic cov_clk,
    input logic cov_writeEnable,
    input logic cov_readEnable,
    input logic cov_writeAck,
    input logic [7:0] cov_address
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

// Check that read strobes only 1 clock
property p_read_strobe_once;
	$rose(cov_readEnable) |=> $fell(cov_readEnable);
endproperty
ast_read_strobe_once : assert property(p_read_strobe_once);
cov_read_strobe_once : cover property(p_read_strobe_once);

// Check that write strobes only 1 clock
property p_write_ack_twice;
	$rose(cov_writeAck) |=> cov_writeAck ##1 $fell(cov_writeAck);
endproperty
ast_write_ack_twice : assert property(p_write_ack_twice);
cov_write_ack_twice : cover property(p_write_ack_twice);

// cover group: log if read and write access occured for all
// documented register address
// Lab: this covergroup will not work properly. Explore why and update.
covergroup covg_RegisterAccess
    @(negedge cov_clk);
	option.name		= "cov_RegisterAccess";
    readMode       : coverpoint cov_readEnable;
    writeMode     : coverpoint cov_writeEnable;
    addressSpace  : coverpoint cov_address;
endgroup

covg_RegisterAccess cov_userifCover = new();




endmodule
