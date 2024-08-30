import cocotb
from bitarray.util import int2ba, ba2int




# Expects cocotb.binary.BinaryValue() argument
def print_cocotb_BinaryValue(SomeValue):
    print("print Cocotb binary string : " + SomeValue.binstr)
    print("print Cocotb integer       : " + "{}".format(SomeValue.integer))
    print("print Cocotb integer in hex: " + "0x{0:{width}x}".format(SomeValue.integer, width=8))
    print("print Cocotb byte buffer ", end='');  print(SomeValue.buff)
    print("print Cocotb byte byte per byte, seen as a serie of int   : ");
    for item in SomeValue.buff:
        print("\t0x{0:2x} ".format(item), end='') # hexadecimal
        print(item)  # decimal
    print()

def build_command_message(command, addr, data):
    message = (command << 43) + (addr << 32) + data
    return cocotb.binary.BinaryValue(value=message, n_bits=48, bigEndian=False)



CRC8_START = 0x0D
CRC_POLY = 0xC6

"""
CRC calculator, using past cumulative CRC (current_crc) and next bye (data).
One byte per function call.
"""
def calculateCRC8_singleCycle(data, current_crc):
    crc = int2ba(current_crc, 8)
    data_bits = int2ba(data, 8)
    poly = int2ba(CRC_POLY, 8)
    for j in range(7, -1, -1):
        if crc[7] != data_bits[j]:
            crc = (crc >> 1) ^ poly
        else:
            crc >>= 1
    return ba2int(crc)

"""
CRC utility
Calculates CRC from n-byte packet.
Usage example
    # Build some n-byte string, for example a read command
    SomeData = build_command_message(0, 4, 0x345678)  # Reading reg at address 0
    # Calculate its CRC
    resultingCRC = get_expected_crc(SomeData.buff)
    # Convert to cocotb format
    crc_to_send = cocotb.binary.BinaryValue(value=resultingCRC, n_bits=8, bigEndian=False)
    # write to UART driver
    await uart_source.write(crc_to_send.buff)
"""
def get_expected_crc(valueArray):
    current_crc = CRC8_START
    for b in valueArray:
        current_crc = calculateCRC8_singleCycle(b, current_crc)

    return current_crc
