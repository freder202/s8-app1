 /*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/
// Convert gray to binary value
module gray2bin #(parameter SIZE = 4)(
input logic [SIZE-1:0] gray,
output logic [SIZE-1:0] bin
);
 //genvar i;
 always_comb
   for(int i=0;i<SIZE;i = i+1) begin
     bin[i] = ^(gray >> i);
   end

endmodule