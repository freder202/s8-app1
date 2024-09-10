 `timescale 1ps/1ps
module Oscillator #(parameter BIT_COUNT = 32, IS_TIMESTAMP=0)(
    input logic enable, reset,
    output logic [BIT_COUNT-1:0] count,
    output logic hasValue    
)/* syntheseis hier="hard" */ ;

    wire r_cycle /* synthesis syn_nocclockbuf=1 */;
    logic r_invert /* synthesis syn_keep=1 */;
    logic r_signalEnd;
    counter oscillatorCounter (.enable(enable), .clk(r_cycle), .reset(reset), .count(count));
    
    generate begin : DelayModule
            if (IS_TIMESTAMP == 1) begin
                DelayChain inst_delayChain(.a(r_cycle), .b(r_invert));
            end else begin
                Delay delay(r_cycle, r_invert);
            end
        end
    endgenerate
    
    assign r_signalEnd = !enable;
    assign r_cycle = enable & r_invert & !reset;
    //AND3 gate(.A(!reset), .B(enable), .C(r_invert), .Y(r_cycle)) /* synthesis syn_nocclockbuf=1 */;

    always_ff @( posedge enable or posedge r_signalEnd) begin
        if (enable) begin
            hasValue <= 0;
        end
        else if (r_signalEnd) begin
            hasValue <= 1;
        end
    end

endmodule
