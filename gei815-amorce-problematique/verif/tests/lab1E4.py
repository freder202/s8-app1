import sys

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
async def lab1E4(dut):


    init.initDebug("lab1E4")

    # L1.E4 - Ajouter l'initialisation des pattes d'entrée et de l'horloge

    await init.initReset(dut)

    # Driver and Sink for the dut UART RX/TX channels
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    # L1.E4 - Start thread for the reply function for the expected UART response.
    Task_returnMessage = await cocotb.start(wait_reply(dut, uart_sink))

    # Send read command
    reg9 = uv.build_command_message(0x0, 0x9, 0x00000000)
    print(f"[DEBUG] {hex(reg9)}")
    await uart_driver.write(reg9.buff)
    await uart_driver.wait()

    # Send CRC
    crc8 = uv.get_expected_crc(reg9.buff)
    crc8bin = cocotb.binary.BinaryValue(value=crc8, n_bits=8, bigEndian=False)
    await uart_driver.write(crc8bin.buff)
    await uart_driver.wait()

    # L1.E4 ait for response to complete or for timeout
    await Task_returnMessage

    #To get the type returned from a Task, you must call task.result()
    packetSplitter = Task_returnMessage.result()
    print(f"[DEBUG] Task_returnMessage type : {type(packetSplitter)}")
    print(packetSplitter)
    print(hex(int(packetSplitter)))

    if (hex(int(packetSplitter)) != hex(0x800badeface)) :
        raise RuntimeError("Not = 0x800badeface")



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
        print(f"[DEBUG] message type : {type(message)}")
        return message


