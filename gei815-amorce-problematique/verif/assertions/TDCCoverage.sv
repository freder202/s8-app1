//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind TDC_dumb TDCCoverage inst_TDCCoverage(
	.cov_reset(reset),
	.cov_clk(clk),
	.cov_hasEvent(o_hasEvent),
	.cov_busy(o_busy),
	.cov_clear(i_clear),
	.cov_trigger(i_trigger),
	.cov_enable(i_enable_channel),
	.cov_TOT(o_pulseWidth),
	.cov_TS(o_timestamp)
	);

module TDCCoverage
	
	(
	input logic cov_reset,
	input logic cov_clk,
    	input logic cov_hasEvent,
	input logic cov_busy,
	input logic cov_clear,
    	input logic cov_trigger,
	input logic cov_enable,
	input logic [31:0] cov_TOT,
	input logic [31:0] cov_TS
	);

default clocking DEFCLK @(posedge cov_clk);
endclocking

endmodule
