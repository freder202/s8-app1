/*
    Author : Thomas Labbé
    Project : Sigma Delta DAQ
    
    Universite de Sherbrooke, 2021
*/

module SyncClk #(parameter 
                 RESET_INTERVAL = 524287, //524287, // ~10 ms 
                 RESET_INTERVAL_LENGTH = 19,
                 COUNTER_SIZE = 19, 
                 CNT_INCREMENT = 1
                 )
                (
                    SyncClkInterface.internal bus,
                    input logic               clk
                );

// States
typedef enum logic [1:0] {STATE_WAIT_FIRST_TRANSMISSION, STATE_WAIT_SECOND_TRANSMISSION, STATE_OK} states;
states fsm_state;


logic [COUNTER_SIZE - 1 : 0] refCnt_r;
logic errorFlag_r;

// Used for CDC. Since bus.clear_error and SyncClearError doesn't have the same clk_ref
logic q_syncClearError;
logic qq_syncClearError;
logic qqq_syncClearError;

// Keep in memory the timer Wrapper
logic [1:0] initWrapCounter;

// Keep the reset in memory
logic oldReset;

// Set all local signals to 0
initial begin
    oldReset = 0;
    q_syncClearError = 0;
    qq_syncClearError = 0;
    qqq_syncClearError = 0;
    errorFlag_r = 0;
    refCnt_r = 0;
    initWrapCounter = 0;
    fsm_state = STATE_WAIT_FIRST_TRANSMISSION;
end

// CDC (clock domain crossing)
task CDC();
    q_syncClearError <= bus.clearError;
    qq_syncClearError <= q_syncClearError;
    qqq_syncClearError <= qq_syncClearError;
endtask // CDC

// Reset signal toggles which causes less electrical noise. 
// Keep it in history in order to xor it 
task ResetDetection();
    oldReset <= bus.resetCyclic;
endtask // ResetDetection 

// Increment the counter
task Sync_Counter();
    if (oldReset != bus.resetCyclic) begin
        refCnt_r <= 0;
    end else begin
        refCnt_r <= refCnt_r + CNT_INCREMENT;
    end
endtask // Sync_Counter 

// Detect when the counter does
task ErrorDetection();
    // Clear received
    if(qqq_syncClearError == 0 && qq_syncClearError == 1) begin
        initWrapCounter <= 0;
        errorFlag_r <= 0;
    end
    // If synch didn't start
    else if(fsm_state != STATE_OK) begin
        if(initWrapCounter == 2'b11) begin
            initWrapCounter <= initWrapCounter;
            errorFlag_r <= 1;
        end else 
        if (refCnt_r[RESET_INTERVAL_LENGTH - 1:0] == RESET_INTERVAL[RESET_INTERVAL_LENGTH - 1:0]) begin 
            initWrapCounter <= initWrapCounter + 1;
            errorFlag_r <= 0;
        end
        else begin
            initWrapCounter <= initWrapCounter;
            errorFlag_r <= 0;
        end
    end else begin
        // Check if clock is still synchronized with host
        if(oldReset != bus.resetCyclic && refCnt_r[RESET_INTERVAL_LENGTH - 1:0] != RESET_INTERVAL[RESET_INTERVAL_LENGTH - 1:0]) begin
            initWrapCounter <= 0;
            errorFlag_r <= 1;
        end
        else begin
            initWrapCounter <= 0;
            errorFlag_r <= errorFlag_r;
        end 
    end
endtask // ErrorDetection

// FSM checking for the start of transmission
task FSM();
    case (fsm_state)
        STATE_WAIT_FIRST_TRANSMISSION : begin
            if(oldReset == 1 && bus.resetCyclic == 0) begin
                fsm_state <= STATE_WAIT_SECOND_TRANSMISSION;
            end
        end

        STATE_WAIT_SECOND_TRANSMISSION : begin
            if(oldReset == 0 && bus.resetCyclic == 1) begin
                fsm_state <= STATE_OK;
            end
        end

        default : begin
            fsm_state <= STATE_OK;
        end
    endcase
endtask // FSM

always_ff @(posedge clk) begin
    CDC();
    ResetDetection();
    Sync_Counter();
    ErrorDetection();
    FSM();
end

assign bus.errorFlag = errorFlag_r;
assign bus.syncCounter = refCnt_r;

endmodule // SyncClk