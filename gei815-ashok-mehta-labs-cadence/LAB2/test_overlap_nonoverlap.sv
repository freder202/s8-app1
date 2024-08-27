module test_overlap_nonoverlap;
bit clk,cstart,req,gnt;

always @(posedge clk)
  $display($stime,,,"clk=%b cstart=%b req=%b gnt=%b",clk,cstart,req,gnt);

always #10 clk = !clk;

sequence sr1;
  req ##2 gnt;
endsequence

`ifdef overlap
property pr1;
  @(posedge clk) cstart |-> sr1;
endproperty 

//Note that if a simulator supports filter on vacuous pass for a 'cover'
//the following property is not needed. You can simply use "property pr1"
//for 'cover' as well.

property pr1_for_cover;
  @(posedge clk) cstart ##0 sr1;
endproperty 

`elsif nonoverlap
property pr1;
  @(posedge clk) cstart |=> sr1;
endproperty 

//Note that if a simulator supports filter on vacuous pass for a 'cover'
//the property pr1_for_cover is not needed. You can simply use "property pr1"
//for 'cover' as well.

property pr1_for_cover;
  @(posedge clk) cstart ##1 sr1;
endproperty 
`endif

reqGnt: assert property (pr1) else $display($stime,,,"\t\t %m FAIL"); 
creqGnt: cover property (pr1_for_cover) $display($stime,,,"\t\t %m PASS"); 

initial
begin
  {cstart,req,gnt}=3'b000;
end

initial
begin
  @(negedge clk); {cstart,req,gnt}=3'b100;
  @(negedge clk); {cstart,req,gnt}=3'b110;
  @(negedge clk); {cstart,req,gnt}=3'b000;
  @(negedge clk); {cstart,req,gnt}=3'b001;

  @(negedge clk); {cstart,req,gnt}=3'b110;
  @(negedge clk); {cstart,req,gnt}=3'b110;
  @(negedge clk); {cstart,req,gnt}=3'b111;
  @(negedge clk); {cstart,req,gnt}=3'b010;
  @(negedge clk); {cstart,req,gnt}=3'b000;
  @(negedge clk); {cstart,req,gnt}=3'b001;

  @(negedge clk); $finish(2);
end

endmodule
