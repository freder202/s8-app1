module test_dut;
bit sys_clk,sys_req;
wire sys_gnt;

/* Instantiate 'dut' */

dut dut1 (
        	.clk(sys_clk), 
		.req(sys_req), 
		.gnt(sys_gnt)
	);

//-------------------------------------
// LAB EXERCISE - START 
//-------------------------------------
//
// Add your code to bind 'dut' with 'dut_property' here.
//

// You need to know the names of the ports in the design and the property module
// to be able to bind them. So, here they are: 

// Design module (dut.v)
// ----------------------
// module dut(clk, req, gnt);
//            input logic clk,req;
//            output logic gnt;

// Property module (dut_property.sv)
// ---------------------------------
//module dut_property(pclk,preq,pgnt);
//input pclk,preq,pgnt;




// Now, follow the directions in the README file to compile/simulate...

//-------------------------------------
// LAB EXERCISE - END 
//-------------------------------------

always @(posedge sys_clk)
  $display($stime,,,"clk=%b req=%b gnt=%b",sys_clk,sys_req,sys_gnt);

always #10 sys_clk = !sys_clk;

initial
begin
                      sys_req = 1'b0;
  @(posedge sys_clk) sys_req = 1'b1; //30
  @(posedge sys_clk) sys_req = 1'b0; //50
  @(posedge sys_clk) sys_req = 1'b0; //70
  @(posedge sys_clk) sys_req = 1'b1; //90
  @(posedge sys_clk) sys_req = 1'b0; //110
  @(posedge sys_clk) sys_req = 1'b0; //130

@(posedge sys_clk); 
@(posedge sys_clk); $finish(2);
end

endmodule
