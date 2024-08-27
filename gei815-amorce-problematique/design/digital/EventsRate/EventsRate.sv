/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

module EventsRate#(parameter
                   COUNTER_LENGTH = 24,
                   CHANNEL_NUMBER = 2,
                   COUNTER_TIME_LENGTH = 32,
                   COUNTER_TIME_VALUE = 5000000)
                (EventsRateInterface.internal bus,
                input                         clk
                );

    logic [COUNTER_LENGTH-1:0]  event_count_temp_r[CHANNEL_NUMBER];
    logic [COUNTER_LENGTH-1:0]  event_count_r[CHANNEL_NUMBER];
    logic [COUNTER_TIME_LENGTH - 1:0] time_count_r;
    
    logic events_rate_ready_r;
    logic clear_counter;
    genvar i;

    generate
        for (i = 0; i < CHANNEL_NUMBER; i = i + 1) begin
            counter #(.BIT_COUNT(COUNTER_LENGTH)) eventsCounter(.clk(clk), .enable(bus.enable[i]), .reset(clear_counter), .count(event_count_temp_r[i]));
        end
    endgenerate

    always_ff @ (posedge clk) begin
        if (bus.clear) begin
            time_count_r = 0;
            clear_counter = 1;
            events_rate_ready_r = 0;
            event_count_r <= '{default:0};
        end 
        else if(bus.read) begin
            event_count_r <= event_count_temp_r;
            events_rate_ready_r = 0;
            time_count_r = 0;
            clear_counter = 1;
        end
        // Put the value of the resets for the ocunters to 0
        else if(clear_counter) begin
            clear_counter = 0;
        end 
        // Send stobe when the counter reach the parameters value. Ideally it should send at each 1 seconds all value of channels
        else if(time_count_r >= COUNTER_TIME_VALUE) begin
            events_rate_ready_r = 1;
        end
        time_count_r++;
    end

    assign bus.event_count = event_count_r;
    assign bus.events_rate_ready = events_rate_ready_r;

endmodule
