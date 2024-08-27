module test_fifo;

wire  [7:0] fifo_data_out;
wire        fifo_full, fifo_empty;
logic       fifo_write, fifo_read, clk, rst_;
logic [7:0] fifo_data_in;

parameter fifo_depth = 8, fifo_width = 8;

fifo #(fifo_depth,fifo_width) fi1 (fifo_data_out,fifo_full,fifo_empty,fifo_write,fifo_read,clk,rst_,
                 fifo_data_in);

bind fifo fifo_property #(fifo_depth,fifo_width) fi1bind 
	(fifo_data_out,fifo_full,fifo_empty,fifo_write,fifo_read,clk,rst_,fifo_data_in);

initial
begin
  clk=0;
  fiforeset;
  fifowrite(10);
  fiforead(9);
  @(posedge clk); 
  @(posedge clk); 
  @(posedge clk); $finish(2);
end

always #5 clk=!clk;

task fiforeset;
  fifo_write=0; fifo_read=0; rst_=1; 
  @(negedge clk); rst_=0;
  @(negedge clk);
  @(negedge clk); rst_=1;
endtask 

task fifowrite;
input int nwrite;
  fifo_read=0;
  for (int i=0; i<=nwrite-1; i++) 
  begin
    @(negedge clk); fifo_write=1; fifo_data_in=i;
      //$display($stime,,,"fifo Write Data = %0d",fifo_data_in);
  end
endtask

task fiforead;
input int nread;
  fifo_write=0;
  repeat(nread)
  begin
    @(negedge clk); fifo_read=1; 
      //$display($stime,,,"fifo Read Data = %0d",fifo_data_out); 
  end
endtask

always @(posedge clk)
  $display($stime,,,"rst_=%b clk=%b fifo_write=%b fifo_read=%b fifo_full=%b fifo_empty=%b wr_ptr=%0d rd_ptr=%0d cnt=%0d",
	rst_,clk,fifo_write,fifo_read,fifo_full,fifo_empty,fi1.wr_ptr,fi1.rd_ptr,fi1.cnt);


endmodule
