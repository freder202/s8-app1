//`define fifo_depth 8
//`define fifo_width 8
                                                                                              
module fifo (fifo_data_out,fifo_full,fifo_empty,fifo_write,fifo_read,clk,rst_,
             fifo_data_in);

parameter fifo_depth=8;
parameter fifo_width=8;

output logic [(fifo_width-1):0] fifo_data_out;
output logic fifo_full, fifo_empty;
input  logic fifo_write, fifo_read, clk, rst_;
input  logic [(fifo_width-1):0] fifo_data_in;

logic [(fifo_width-1):0] fifomem [0:(fifo_depth-1)];

logic [3:0] wr_ptr, rd_ptr;
logic [3:0] cnt;                         

always @(posedge clk or negedge rst_)
  if (!rst_) begin
    rd_ptr  <= 0;                          
    wr_ptr  <= 0;
    cnt   <= 0;
`ifndef check1
    fifo_empty <= 1;
`endif
    fifo_full  <= 0;
  end
  else begin
    case ({fifo_write, fifo_read})
      2'b00: ;     // everyone's sleeping! 
      2'b01: begin // read
               if (cnt>0) begin          
                 rd_ptr <= rd_ptr + 1;       
                 cnt  <= cnt  - 1;       
               end                       
`ifdef check2
               if (cnt==0) fifo_empty <= 1;   
`else 
`ifdef check5
               if (cnt==1) fifo_empty <= 1;   
	       rd_ptr <= rd_ptr+1;
`else
               if (cnt==1) fifo_empty <= 1;   
`endif
`endif
               fifo_full <= 0;
             end
      2'b10: begin // write
               if (cnt< fifo_depth) begin        
                 fifomem[wr_ptr] <= fifo_data_in;
                 wr_ptr <= wr_ptr + 1;
                 cnt  <= cnt  + 1;
               end
`ifdef check3
               if (cnt>(fifo_depth-1)) fifo_full <= 1;   
`else 
`ifdef check4
               if (cnt>=(fifo_depth-1)) fifo_full <= 1;   
	       wr_ptr <= wr_ptr+1;
`else
               if (cnt>=(fifo_depth-1)) fifo_full <= 1;   
`endif
`endif
               fifo_empty <= 0;
             end
      2'b11: // write && read
             //You cannot write if cnt is full; so read only
               if (cnt>(fifo_depth-1)) begin
                 rd_ptr  <= rd_ptr + 1;
                 cnt   <= cnt  - 1;
               end
            //You cannot read if cnt is empty; so write only
               else if (cnt<1) begin
                 fifomem[wr_ptr] <= fifo_data_in;
                 wr_ptr  <= wr_ptr + 1;
                 cnt   <= cnt  + 1;
               end
            //else write and read both
               else begin
                 fifomem[wr_ptr] <= fifo_data_in;
                 wr_ptr  <= wr_ptr + 1;
                 rd_ptr  <= rd_ptr + 1;
               end
    endcase
  end

assign fifo_data_out = fifomem[rd_ptr];

endmodule
