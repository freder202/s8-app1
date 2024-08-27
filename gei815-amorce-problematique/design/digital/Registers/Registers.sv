import registers_sv_pkg::*;
`timescale 1ps/1ps
`define registers_addr_width 4
`define registers_data_width 32
/* verilator lint_off REDEFMACRO */
module Registers#(
		parameter		   width       = `registers_data_width,
	    parameter		   addressWidth = `registers_addr_width
	    )(
	      input logic [addressWidth-1:0] 	address,
	      input logic 		   			 	writeEnable,
	      input logic [width-1:0] 	   		writeData,
	      input logic 		   				readEnable,
	      input logic 		   				clk,
	      input logic 		   				rstn,
		  input logic 			            writeAdmin,
		  output logic [width-1:0] 	   		readData,
		  output logic  					writeAck,
		  output logic						syncClearStrobe, // Strobe to clear the flag error
		  output logic						update_enable_channel // Strobe update channel
	      );				

   registers_struct_type registers;
   
	always_ff @ (posedge clk or negedge rstn) 
		begin
			if(rstn==0) begin
				registers <= reset_registers(registers);
				readData <= 0;
				writeAck <= 0;
				syncClearStrobe <= 0;
				update_enable_channel <= 0;	  
			end		
			else begin
				syncClearStrobe <= 0;
				update_enable_channel <= 0;	  
				// Reading has higher priority than writing
				if(readEnable) begin
					readData <= read_registers(registers, int'(address));
				end
				else if (writeEnable) begin
					// Check which type of write it is, write with all permission or not
					if (writeAdmin == 1) begin registers <= write_on_read_only_registers(writeData,int'(address),registers); end 
					else begin registers <= write_registers(writeData,int'(address),registers); end
			 		
					writeAck <= 1; // Signal that writing occured

					//Generate strobe
					if (int'(address) == DisableFlagSync_addr && writeData == 1) begin
						registers <= write_on_read_only_registers(0, int'(FlagSyncError_addr),registers);
						syncClearStrobe <= 1;
					end
					case (int'(address)) 
						DisableFlagSync_addr : begin if(writeData == 1) begin syncClearStrobe <= 1; end end
						ActiveChannels_addr : begin  end
					endcase
					if (int'(address) == ActiveChannels_addr) begin
						update_enable_channel <= 1;
					end
		 		end
				else if (writeAck) begin
					writeAck <= 0; // Reset flag is nothing to write on next clock cycle
					registers <= reset_write_only_registers(registers);
				end
			end
		end
endmodule
