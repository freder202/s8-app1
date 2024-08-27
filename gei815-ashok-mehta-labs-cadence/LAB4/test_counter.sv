module test_counter;

logic clk, rst_, ld_cnt_, updn_cnt, count_enb;
logic [7:0] data_in;
wire [7:0] data_out;

int seed1;

counter  upc(
  clk, rst_, ld_cnt_, updn_cnt, count_enb,
  data_in,
  data_out
  );

bind counter counter_property bind_inst (
  clk, rst_, ld_cnt_, updn_cnt, count_enb,
  data_in,
  data_out
  );

initial
begin
  clk=1'b0;
  counter_init;
  	count_up(100,10);
  repeat (2) @(posedge clk);
	count_down(100,10);
  repeat (2) @(posedge clk);
  @(posedge clk); $finish(2);
end

always @(posedge clk) 
   $display($stime,,,"rst_=%b clk=%b count_enb=%b ld_cnt_=%b updn_cnt=%b DIN=%0d DOUT=%0d",
   rst_, clk, count_enb, ld_cnt_, updn_cnt, data_in, data_out);

always #5 clk=!clk;

task counter_init;
  rst_=1'b1; ld_cnt_=1'b1; count_enb=1'b0; updn_cnt=1'b1;

  @(negedge clk); rst_=1'b0; 
  @(negedge clk);
  @(negedge clk); rst_=1'b1; 
  @(negedge clk); data_in=8'b0; ld_cnt_=1'b0;
  @(negedge clk);
endtask

task count_up;
input logic [7:0] din;
input int count; 
  @(negedge clk); data_in=din; ld_cnt_=1'b0; 
  @(negedge clk); ld_cnt_=1'b1; count_enb=1'b1; updn_cnt=1'b1;
  repeat (count-1) @(negedge clk); 
  @(negedge clk); count_enb=1'b0;
endtask

task count_down;
input logic [7:0] din;
input int count; 
  @(negedge clk); data_in=din; ld_cnt_=1'b0;
  @(negedge clk); ld_cnt_=1'b1; count_enb=1'b1; updn_cnt=1'b0;
  repeat (count-1) @(negedge clk); 
  @(negedge clk); count_enb=1'b0;
endtask

endmodule
