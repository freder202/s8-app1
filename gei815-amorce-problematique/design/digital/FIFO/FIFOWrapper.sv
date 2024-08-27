`define DATA_LENGTH 32
`define FIFO_LENGTH 68

package FIFOWrapper;
    typedef struct packed {
        TDCTypes::TDC_CHANNEL channel;
        logic [`DATA_LENGTH - 1:0] ToT;
        logic [`DATA_LENGTH - 1:0] timestamp;
    } FIFO_internal_t;

    typedef union packed {
        FIFO_internal_t FIFO;
        logic [`FIFO_LENGTH - 1:0] data;
    } FIFO_t;
endpackage 