//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////


// Bind statement usage in mixed-langage environments
//			https://www.youtube.com/watch?v=VuBqJoTRYyU


bind TransmitterControl TransmitterControlCoverage u_TransmitterControlCoverage(
	.reset(reset),
	.clk(clk),
	.i_UartReplyGo(i_UartReplyGo),
	.r_UartReplyAck(r_UartReplyAck),
	.r_DebugSampleRead(r_DebugSampleRead),
	.s_UartTxGo(s_UartTxGo),
	.i_UartTxDone(i_UartTxDone)
	);

module TransmitterControlCoverage
	//#(parameter g_ChannelId = 15)
	(
	input reset,
	input clk,
    input i_UartReplyGo,
    input r_UartReplyAck,
    input r_DebugSampleRead,
    input s_UartTxGo,
    input i_UartTxDone
	);


default clocking DEFCLK @(posedge clk);
endclocking

property p_uart_reply_ack;
	i_UartReplyGo |=> ##[1:$] r_UartReplyAck;
endproperty
ast_uart_reply_ack : assert property(p_uart_reply_ack);

property p_uart_go_followed_by_done;
	s_UartTxGo |=> ##[1:$] i_UartTxDone;
endproperty
ast_uart_go_followed_by_done : assert property(p_uart_go_followed_by_done);

covergroup covg_UartTx @(posedge clk iff reset);
	option.name		= "cov_UartTx";
    fifoAccess     : coverpoint r_DebugSampleRead;
endgroup
covg_UartTx cov_UartTx = new();

endmodule



bind CommonModules CommonCoverage u_CommonCoverage(
	.reset(reset),
	.clk(clk),
	.userif_Mode(userif_Mode),
	.userif_SampleRead(userif_SampleRead)
	);

module CommonCoverage
	//#(parameter g_ChannelId = 15)
	(
	input reset,
	input clk,
    input [1:0] userif_Mode,
    input userif_SampleRead
	);


default clocking DEFCLK @(posedge clk);
endclocking

covergroup covg_userifCover @(posedge clk iff reset);
	option.name		= "cov_userifCover";
    fifoAccess     : coverpoint userif_SampleRead;
	RegisterAcess	: coverpoint userif_Mode {
		bins ReadAccess  = {0};
		bins WriteAccess = {1};
		}
endgroup
covg_userifCover cov_userifCover = new();

endmodule
