//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    GEI815
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


bind TDC_dumb TDCCoverage u_TDCCoverage(
	.cov_reset(reset),
	.cov_clk(clk),
	.cov_hasEvent(bus.hasEvent),
	.cov_busy(busy),
	.cov_clear(bus.clear),
	.cov_trigger(trigger),
	.cov_enable(enable_channel),
	.cov_TOT(bus.timeOverThreshold),
	.cov_TS(bus.timestamp)
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
