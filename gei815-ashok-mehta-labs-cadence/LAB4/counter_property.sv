/************************************************************************\
|*                                                                      *|
|*    Copyright (c) 2008  Ashok B.Mehta. All rights reserved.           *|
|*                                                                      *|
|*  This example code should be used only for illustration purpose      *|
|*  This material is not to be reproduced,  copied,  or used  in any    *|
|*  manner without the authorization of the author's written permission *|
|*                                                                      *|
|*  Author: Ashok B. Mehta  (Email:ashokdefineview.com)                 *|
\************************************************************************/

module counter_property (
  input clk, rst_, ld_cnt_, updn_cnt, count_enb,
  input [7:0] data_in,
  input logic [7:0] data_out
  );

//------------------------------------

//        CHECK # 1. Check that when 'rst_' is asserted (==0) that data_out == 8'b0

//------------------------------------
`ifdef check1
property counter_reset;
  @(posedge clk) data_in |=> data_out; //DUMMY - REMOVE this line and code correct assertion 
endproperty

counter_reset_check: assert property(counter_reset) 
  else $display($stime,,,"\t\tCOUNTER RESET CHECK FAIL:: rst_=%b data_out=%0d \n",
				rst_,data_out);
`endif

//------------------------------------
//Check for count to hold if count_enb is disabled 

//        CHECK # 2. Check that if ld_cnt_ is deasserted (==1) and count_enb is not enabled
//                   (==0) that data_out HOLDS it's previous value.
//                   Disable this property 'iff (!rst)'

//------------------------------------
`ifdef check2
property counter_hold;
  @(posedge clk) data_in |=> data_out; //DUMMY - REMOVE  this line and code correct assertion
endproperty

counter_hold_check: assert property(counter_hold) 
  else $display($stime,,,"\t\tCOUNTER HOLD CHECK FAIL:: counter HOLD \n");
`endif

//------------------------------------

//        CHECK # 3. Check that if ld_cnt_ is deasserted (==1) and count_enb is enabled
//                   (==1) that if updn_cnt==1 the count goes UP and
//                              if updn_cnt==0 the count goes DOWN.
//                   Disable this property 'iff (!rst)'

//------------------------------------

`ifdef check3
property counter_count;
  @(posedge clk) data_in |=> data_out; //DUMMY - REMOVE  this line and code correct assertion
endproperty

counter_count_check: assert property(counter_count) 
  else $display($stime,,,"\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n"); 
`endif

endmodule
