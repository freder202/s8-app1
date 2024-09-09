// Automatically generated
// with the command '/home/mtetrault/.local/bin/ipxact2systemverilog -s registers.xml -d ../'
//
// Do not manually edit!
//
/* verilator lint_off REDEFMACRO */
package registers_sv_pkg;


const int addr_width = 4;
const int data_width = 32;

const int DataMode_addr = 0;
const int TensionMode_addr = 1;
const int EnableCntRate_addr = 2;
const int EnableEventCntRate_addr = 3;
const int Threshold_addr = 4;
const int SrcSelected_addr = 5;
const int FlagSyncError_addr = 6;
const int DisableFlagSync_addr = 7;
const int ActiveChannels_addr = 8;
const int ProductKey_addr = 9;

//synopsys translate_off
const int registers_regAddresses [10] = '{
     DataMode_addr,
     TensionMode_addr,
     EnableCntRate_addr,
     EnableEventCntRate_addr,
     Threshold_addr,
     SrcSelected_addr,
     FlagSyncError_addr,
     DisableFlagSync_addr,
     ActiveChannels_addr,
     ProductKey_addr};

const string registers_regNames [10] = '{
      "DataMode",
      "TensionMode",
      "EnableCntRate",
      "EnableEventCntRate",
      "Threshold",
      "SrcSelected",
      "FlagSyncError",
      "DisableFlagSync",
      "ActiveChannels",
      "ProductKey"};
const reg registers_regUnResetedAddresses [10] = '{
   1'b1,
   1'b1,
   1'b1,
   1'b1,
   1'b1,
   1'b1,
   1'b1,
   1'b1,
   1'b0,
   1'b0};

//synopsys translate_on



typedef struct packed {
   bit [1:0] Mode;//bits [1:0]
} DataMode_struct_type;


typedef struct packed {
   bit [1:0] Mode;//bits [1:0]
} TensionMode_struct_type;


typedef struct packed {
   bit [0:0] Enable;//bits [0:0]
} EnableCntRate_struct_type;


typedef struct packed {
   bit [0:0] Enable;//bits [0:0]
} EnableEventCntRate_struct_type;


typedef struct packed {
   bit [31:0] Value;//bits [31:0]
} Threshold_struct_type;


typedef struct packed {
   bit [0:0] Mode;//bits [0:0]
} SrcSelected_struct_type;


typedef struct packed {
   bit [0:0] Value;//bits [0:0]
} FlagSyncError_struct_type;


typedef struct packed {
   bit [0:0] Mode;//bits [0:0]
} DisableFlagSync_struct_type;


typedef struct packed {
   bit [15:0] ChannelEnable;//bits [15:0]
   //bit [0:0] MasterSwitch;//bits [0:0]
} ActiveChannels_struct_type;

typedef struct packed {
   bit [31:0] Value;//bits [31:0]
} ProductKey_struct_type;

const DataMode_struct_type DataMode_reset_value = 0;
const TensionMode_struct_type TensionMode_reset_value = 0;
const EnableCntRate_struct_type EnableCntRate_reset_value = 0;
const EnableEventCntRate_struct_type EnableEventCntRate_reset_value = 0;
const Threshold_struct_type Threshold_reset_value = 0;
const SrcSelected_struct_type SrcSelected_reset_value = 0;
const FlagSyncError_struct_type FlagSyncError_reset_value = 0;
const DisableFlagSync_struct_type DisableFlagSync_reset_value = 0;
const ActiveChannels_struct_type ActiveChannels_reset_value = 16'h0;
const ProductKey_struct_type ProductKey_reset_value = 32'hBADEFACE;

typedef struct packed {
   DataMode_struct_type DataMode;
   TensionMode_struct_type TensionMode;
   EnableCntRate_struct_type EnableCntRate;
   EnableEventCntRate_struct_type EnableEventCntRate;
   Threshold_struct_type Threshold;
   SrcSelected_struct_type SrcSelected;
   FlagSyncError_struct_type FlagSyncError;
   DisableFlagSync_struct_type DisableFlagSync;
   ActiveChannels_struct_type ActiveChannels;
   ProductKey_struct_type ProductKey;
} registers_struct_type;

function bit [31:0] read_registers(registers_struct_type registers,int address);
      bit [31:0]  r;
      r = 0;
      case(address)
         DataMode_addr: r[$bits(registers.DataMode)-1:0] = registers.DataMode;
         TensionMode_addr: r[$bits(registers.TensionMode)-1:0] = registers.TensionMode;
         EnableCntRate_addr: r[$bits(registers.EnableCntRate)-1:0] = registers.EnableCntRate;
         EnableEventCntRate_addr: r[$bits(registers.EnableEventCntRate)-1:0] = registers.EnableEventCntRate;
         Threshold_addr: r[$bits(registers.Threshold)-1:0] = registers.Threshold;
         SrcSelected_addr: r[$bits(registers.SrcSelected)-1:0] = registers.SrcSelected;
         FlagSyncError_addr: r[$bits(registers.FlagSyncError)-1:0] = registers.FlagSyncError;
         DisableFlagSync_addr: r[$bits(registers.DisableFlagSync)-1:0] = registers.DisableFlagSync;
         ActiveChannels_addr: r[$bits(registers.ActiveChannels)-1:0] = registers.ActiveChannels;
         ProductKey_addr: r[$bits(registers.ProductKey)-1:0] = registers.ProductKey;
        default: r =0;
      endcase
      return r;
endfunction

function registers_struct_type write_registers(bit [31:0] data, int address,
                                               registers_struct_type registers);
   registers_struct_type r;
   r = registers;
   case(address)
         DataMode_addr: r.DataMode = data[$bits(registers.DataMode)-1:0];
         TensionMode_addr: r.TensionMode = data[$bits(registers.TensionMode)-1:0];
         EnableCntRate_addr: r.EnableCntRate = data[$bits(registers.EnableCntRate)-1:0];
         EnableEventCntRate_addr: r.EnableEventCntRate = data[$bits(registers.EnableEventCntRate)-1:0];
         Threshold_addr: r.Threshold = data[$bits(registers.Threshold)-1:0];
         SrcSelected_addr: r.SrcSelected = data[$bits(registers.SrcSelected)-1:0];
         //FlagSyncError_addr: r.FlagSyncError = data[$bits(registers.FlagSyncError)-1:0];
         DisableFlagSync_addr: r.DisableFlagSync = data[$bits(registers.DisableFlagSync)-1:0];
         ActiveChannels_addr: r.ActiveChannels = data[$bits(registers.ActiveChannels)-1:0];
   endcase // case address
   return r;
endfunction

function registers_struct_type reset_write_only_registers(registers_struct_type registers);
   registers_struct_type r;
   r = registers;
   
   // Strobe registers
   r.DisableFlagSync = DisableFlagSync_reset_value[$bits(registers.DisableFlagSync)-1:0];
   return r;
endfunction

function registers_struct_type write_on_read_only_registers(bit [31:0] data, int address,
                                                            registers_struct_type registers);
   registers_struct_type r;
   r = registers;
   case(address)
         DataMode_addr: r.DataMode = data[$bits(registers.DataMode)-1:0];
         TensionMode_addr: r.TensionMode = data[$bits(registers.TensionMode)-1:0];
         EnableCntRate_addr: r.EnableCntRate = data[$bits(registers.EnableCntRate)-1:0];
         EnableEventCntRate_addr: r.EnableEventCntRate = data[$bits(registers.EnableEventCntRate)-1:0];
         Threshold_addr: r.Threshold = data[$bits(registers.Threshold)-1:0];
         SrcSelected_addr: r.SrcSelected = data[$bits(registers.SrcSelected)-1:0];
         FlagSyncError_addr: r.FlagSyncError = data[$bits(registers.FlagSyncError)-1:0];
         DisableFlagSync_addr: r.DisableFlagSync = data[$bits(registers.DisableFlagSync)-1:0];
         ActiveChannels_addr: r.ActiveChannels = data[$bits(registers.ActiveChannels)-1:0];
         ProductKey_addr: r.ProductKey = data[$bits(registers.ProductKey)-1:0];
   endcase // case address
   return r;
endfunction

function registers_struct_type reset_registers(registers_struct_type registers);
   registers_struct_type r;
   r = registers;
   r.DataMode = DataMode_reset_value[$bits(registers.DataMode)-1:0];
   r.TensionMode = TensionMode_reset_value[$bits(registers.TensionMode)-1:0];
   r.EnableCntRate = EnableCntRate_reset_value[$bits(registers.EnableCntRate)-1:0];
   r.EnableEventCntRate = EnableEventCntRate_reset_value[$bits(registers.EnableEventCntRate)-1:0];
   r.Threshold = Threshold_reset_value[$bits(registers.Threshold)-1:0];
   r.SrcSelected = SrcSelected_reset_value[$bits(registers.SrcSelected)-1:0];
   r.FlagSyncError = FlagSyncError_reset_value[$bits(registers.FlagSyncError)-1:0];
   r.DisableFlagSync = DisableFlagSync_reset_value[$bits(registers.DisableFlagSync)-1:0];
   r.ActiveChannels = ActiveChannels_reset_value[$bits(registers.ActiveChannels)-1:0];
   r.ProductKey=ProductKey_reset_value[$bits(registers.ProductKey)-1:0];
   return r;
endfunction

endpackage //registers_sv_pkg
