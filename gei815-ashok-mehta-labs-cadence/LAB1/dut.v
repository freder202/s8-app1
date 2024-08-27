/* A very simple behavioral Verilog model that acts as 
   the DUT driving a simple req/gnt protocol
*/

module dut(clk, req, gnt);
input logic clk,req;
output logic gnt;

initial
begin
  gnt=1'b0;
end

initial
begin
	@(posedge req);
  	  @(negedge clk); gnt=1'b0;
	  @(negedge clk); gnt=1'b1;

	@(posedge req);
  	  @(negedge clk); gnt=1'b0;
	  @(negedge clk); gnt=1'b0;
end

endmodule
