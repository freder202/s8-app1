`define rd_ptr test_fifo.fi1.rd_ptr
`define wr_ptr test_fifo.fi1.wr_ptr
`define cnt test_fifo.fi1.cnt

module fifo_property (
	input logic [7:0] fifo_data_out,
	input logic       fifo_full, fifo_empty,
	input logic       fifo_write, fifo_read, clk, rst_,
	input logic [7:0] fifo_data_in
                  );

parameter fifo_depth=8;
parameter fifo_width=8;
                                                                                              
//      ------------------------------------------
//        1. Check that on reset,
//                      rd_ptr=0; wr_ptr=0; cnt=0; fifo_empty=1 and fifo_full=0
//      ------------------------------------------
`ifdef check1
property check_reset;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
check_resetP: assert property (check_reset) else $display($stime,"\t\t FAIL::check_reset\n");
`endif

//      ------------------------------------------
//        2. Check that fifo_empty is asserted the same clock that fifo 'cnt' is 0.
//           Disable this property 'iff (!rst)'
//      ------------------------------------------
`ifdef check2
property fifoempty;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
fifoemptyP: assert property (fifoempty) else $display($stime,"\t\t FAIL::fifo_empty condition\n");
`endif

//      ------------------------------------------
//        3. Check that fifo_full is asserted any time fifo 'cnt' is greater than 7.
//           Disable this property 'iff (!rst)'
//      ------------------------------------------
`ifdef check3
property fifofull;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
fifofullP: assert property (fifofull) else $display($stime,"\t\t FAIL::fifo_full condition\n");
`endif

//      ------------------------------------------
//        4. Check that if fifo is full and you attempt to write (but not read) that
//           the wr_ptr does not change.
//      ------------------------------------------
`ifdef check4
property fifo_full_write_stable_wrptr;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
fifo_full_write_stable_wrptrP: assert property (fifo_full_write_stable_wrptr) 
	else $display($stime,"\t\t FAIL::fifo_full_write_stable_wrptr condition\n");
`endif

`ifdef check5
//      ------------------------------------------
//        5. Check that if fifo is empty and you attempt to read (but not write) that
//           the rd_ptr does not change.
//      ------------------------------------------
property fifo_empty_read_stable_rdptr;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
fifo_empty_read_stable_rdptrP: assert property (fifo_empty_read_stable_rdptr) 
	else $display($stime,"\t\t FAIL::fifo_empty_read_stable_rdptr condition\n");
`endif

//      ------------------------------------------
//        6. Write a property to Warn on write to a full fifo
//	This property will give Warning with all simulations  
//      ------------------------------------------
`ifdef check6
property write_on_full_fifo;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
write_on_full_fifoP: assert property (write_on_full_fifo)
	else $display($stime,"\t\t WARNING::write_on_full_fifo\n");
`endif

//      ------------------------------------------
//        7. Write a property to Warn on read from an empty fifo
//	This property will give Warning with all simulations  
//      ------------------------------------------
`ifdef check7
property read_on_empty_fifo;
  @(posedge clk) !rst_ |-> `rd_ptr==0; //DUMMY... remove this line and replace it with correct check
endproperty
read_on_empty_fifoP: assert property (read_on_empty_fifo) 
	else $display($stime,"\t\t WARNING::read_on_empty_fifo condition\n");
`endif

endmodule
