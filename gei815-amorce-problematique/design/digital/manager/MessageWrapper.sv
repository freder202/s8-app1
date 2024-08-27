
`define DATA_LENGTH 32
`define COMMAND_LENGTH 5
`define DATA_TYPE_LENGTH 5
`define PACKET_LENGTH 48
`define PACKET_NUMBER_LENGTH 2
`define ADDR_REG_LENGTH 8


import TDCTypes::*;

package MessageWrapper;
    typedef enum logic[`COMMAND_LENGTH - 1:0] { 
        read_register,
        write_register,
        read_events,
        read_events_rate,
        reset_events_rate
    } command_t;

    typedef enum logic[`DATA_TYPE_LENGTH - 1:0] {
        nack,
        read_reg,
        ack_write_reg,
        send_events,
        events_count,
        ack_reset_events_rate
    } data_type_t;

    typedef struct packed {
        data_type_t data_type;
        logic [2:0] reserved1;
        logic [`PACKET_NUMBER_LENGTH - 1:0] packet_number;
        TDCTypes::TDC_CHANNEL channel;
        logic [1:0] reserved2;
        logic [`DATA_LENGTH - 1:0] data;

    } message_write_t;

    typedef struct packed {
        command_t command;
        logic [2:0] reserved1;
        logic [`ADDR_REG_LENGTH - 1 : 0] addr;
        logic [`DATA_LENGTH - 1:0] data;

    } message_read_t;

    // Union des deux
    typedef union packed {
        message_write_t write;
        message_read_t  read;
        logic [`PACKET_LENGTH - 1:0] packet;
    } message_t;

endpackage // MessageWrapper