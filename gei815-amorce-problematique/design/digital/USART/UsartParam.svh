`ifndef usart_params_h
`define usart_params_h
localparam  USART_DATA_LENGTH = 48,
            USART_BAUD_RATE   = 115_200,
            USART_CLK_FREQ    = 1_000_000,
            USART_MSG_LENGTH = 48,
            USART_PARITY_CHECK = 1,
            USART_PARITY_MODE = 1;         // 1 for odd, 0 for even
`endif