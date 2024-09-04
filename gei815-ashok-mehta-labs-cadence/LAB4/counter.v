module counter (
  input clk, rst_, ld_cnt_, updn_cnt, count_enb,
  input [7:0] data_in,
  output logic [7:0] data_out
  );

always @(posedge clk or negedge rst_)
begin
  if (!rst_)
    begin
    `ifndef check1
       data_out <= 0;
    `endif
     end
  
  else
  begin
  
    //LOAD DATA 
    if (!ld_cnt_)  
      data_out <= data_in;
  
    //HOLD DATA
    `ifndef check2
     else if (!count_enb)
    	data_out <= data_out;
    `endif
  
    //COUNT DATA
    `ifdef check3
    else
      case (updn_cnt)
        1'b1: data_out <= data_out - 1;
        1'b0: data_out <= data_out + 1;
      endcase
    `else
    else
      case (updn_cnt)
        1'b1: data_out <= data_out + 1;
        1'b0: data_out <= data_out - 1;
      endcase
    `endif
  
  end
end

endmodule
