//////////////////////////////////////////////////////////////////////////////////
// DelayChain Module:  creates an inverter chain to have a signal delay
// parameters:
//  numElements: Number of elements in the inverter chain
//  delay_ps: The delay of each inverter to use in behavorial simulation. Ignored at synthesis
// ports:
//  a [in] : the input signal to delay
// b [out] : the delayed input signal
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ps/1ps
// FIXME: Currently does not work in synthesis with Libero-SoC.
/* synthesis translate_off */
module DelayChain #(parameter numElements = 3, delay_ps=11)(
    input logic a,
    output logic b
    );

    /* verilator lint_off UNOPT */
    wire connect [numElements:0]/* synthesis syn_keep=1 alspreserve=1 */; 
    /* lint_on */
    assign connect[0] = a;
    assign b = connect[numElements];
    
    generate
        for(genvar i = 1; i < numElements; i++) begin : generateDelayChain
            //`ifndef LIBERO
            //    INV inv(connect[i],connect[i+1]);
            //`else
                not #(delay_ps) (connect[i+1], connect[i]);
            //`endif
            
        end
    endgenerate
endmodule
/* synthesis translate_on */
