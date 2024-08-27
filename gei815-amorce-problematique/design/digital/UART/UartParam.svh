`ifndef uart_params_h
`define uart_params_h
localparam  UART_DATA_LENGTH = 8,
            UART_BAUD_RATE   = 1_000_000,
            UART_CLK_FREQ    = 100_000_000,
            //UART_MSG_LENGTH = 48,
            UART_PARITY_CHECK = 0,
            UART_PARITY_MODE = 1;         // 1 for odd, 0 for even
`endif