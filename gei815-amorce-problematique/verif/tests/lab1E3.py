import cocotb
from cocotb.clock import Clock
import os
import pydevd_pycharm
from cocotb.triggers import Join
from cocotbext.uart import UartSource, UartSink
from utilsVerif import print_cocotb_BinaryValue
import utilsVerif as uv
from cocotb.log import SimLog

#Homemade module
import init


# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def lab1E3(dut):
    print("Uart instance demo")

    init.initDebug()
    await init.initReset(dut)

    # Driver and Sink for the dut UART RX/TX channels
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)


    #Send read command
    reg9 = uv.build_command_message(0x0,0x9,0x00000000)
    print(f"[DEBUG] {hex(reg9)}")
    await uart_driver.write(reg9.buff)
    await uart_driver.wait()

    #Send CRC
    crc8 = uv.get_expected_crc(reg9.buff)
    crc8bin = cocotb.binary.BinaryValue(value=crc8, n_bits=8, bigEndian=False)
    await uart_driver.write(crc8bin.buff)
    await uart_driver.wait()


# L.E4 function to wait for response message
async def wait_reply(dut, uart_sink):

    # Non-infinite wait loop. Throw cocotb exception if timeout is reached (to do)
    for x in range(0, 100):
        if(uart_sink.count() >= 7): ## 6 octets du message + le CRC
            break;
        await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

    if(x == 99):
        print("Timeout")
        logger = SimLog("cocotb.Test")
        logger.info("Timeout for wait reply")
        raise RuntimeError("Timeout for wait reply")
        # or use plain assert.
        #assert False, "Timeout for wait reply"
        return None

    else:
        # cocotbext-uart returns byteArray. Convert to bytes first, then to Binary value for uniformity.
        message_bytes = bytes(await uart_sink.read(count=6))
        message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
        print("After a wait of " + str(x) + "000 clocks, received message: ", end='')
        print("0x{0:0{width}x}".format(message.integer, width=12))
        return message


