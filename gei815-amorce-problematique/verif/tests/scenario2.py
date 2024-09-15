import sys

import random
import cocotb
from cocotb.clock import Clock
import os
import pydevd_pycharm
from cocotbext.uart import UartSource, UartSink
from cocotb.triggers import Join, Timer
from utilsVerif import print_cocotb_BinaryValue
import utilsVerif as uv
from cocotb.log import SimLog
import MMC_CRC8 as MMC

#Homemade module
import init

# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def scenario2(dut):
    
    init.initDebug("scenario2 - CHECK CRC8 with a load of 96 values")

    #FROM design/digital/UART/packet_merger.sv
    CRC8 = MMC.MMC_CRC8(dut.inst_packet_merger.inst_crc_calc)
    CRC8.start()

    # L1.E4 - Ajouter l'initialisation des pattes d'entrée et de l'horloge
    await init.initReset(dut)

    # Driver and Sink for the dut UART RX/TX channels
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    message_queue = cocotb.queue.Queue()
    # L1.E4 - Start thread for the reply function for the expected UART response.


    # Loop 96 times to send a command to the DUT and wait for the response
    for i in range(96):
        Thread_uart = cocotb.start_soon(coro=wait_reply(dut, uart_sink, message_queue))
        # Send read command
        # value = random.randint(0, 0xFFFFFFFF)
        reg9 = uv.build_command_message(0x0, i, i)
        print(f"[DEBUG] Loop {i+1} ------------------------")
        print(f"[DEBUG] Loop {i+1}: Sending command {hex(reg9)}")
        await uart_driver.write(reg9.buff)
        await uart_driver.wait()

        # Send CRC
        crc8 = uv.get_expected_crc(reg9.buff)
        crc8bin = cocotb.binary.BinaryValue(value=crc8, n_bits=8, bigEndian=False)
        await uart_driver.write(crc8bin.buff)
        await uart_driver.wait()

        # Wait for response to complete or for timeout
        # Task_returnMessage = await cocotb.start(wait_reply(dut, uart_sink, message_queue))
        Task_returnMessage = await Thread_uart
        packetSplitter = Task_returnMessage
        print(f"[DEBUG] Loop {i+1}: Received response {hex(int(packetSplitter))}")

        # Optional: Add a small delay between iterations if needed
        # print(f"[DEBUG] Loop {i+1}: Received response {await message_queue.get()} \n\n\n")
        
        # while message_queue.empty():
        #     # print("are we empty ?")
        #     await Timer(10, 'ns')
        # await wait_reply
        
        # message_queue.pop()
            

    await Timer(1500, 'us')
    print("ici on fail cool")


async def wait_reply(dut, uart_sink, message_queue):
    # Non-infinite wait loop. Throw cocotb exception if timeout is reached (to do)
    for x in range(0, 100):
        print(x)
        if uart_sink.count() >= 7:  # 6 octets du message + le CRC
            break
        await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

    if x == 99:
        print("Timeout")
       
        logger = SimLog("cocotb.Test")
        logger.info("Timeout for wait reply")
        raise RuntimeError("Timeout for wait reply")
        # await message_queue.put(None)
        return None
    else:
        # cocotbext-uart returns byteArray. Convert to bytes first, then to Binary value for uniformity.
        message_bytes = bytes(await uart_sink.read(count=6))
        crc_bytes = bytes(await uart_sink.read(count=1))
        message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
        print("After a wait of " + str(x) + "000 clocks, received message: ", end='')
        print("0x{0:0{width}x}".format(message.integer, width=12))
        print(f"[DEBUG] message type : {type(message)}")
        # message_queue.put(message)
        return message

async def t_uart_test(dut, uart_sink,message_queue):
    Task_returnMessage = await cocotb.start(wait_reply(dut, uart_sink,message_queue))

    packetSplitter = await Task_returnMessage
    print(f"[DEBUG] Task_returnMessage type : {type(packetSplitter)}")
    print(packetSplitter)
    print(hex(int(packetSplitter)))

