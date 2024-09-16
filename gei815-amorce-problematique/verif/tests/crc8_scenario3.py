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
async def crc8_scenario3(dut):
    
    init.initDebug("scenario3 - CHECK send a good message then another with a bad crc")

    #FROM design/digital/UART/packet_merger.sv
    CRC8 = MMC.MMC_CRC8(dut.inst_packet_merger.inst_crc_calc)
    CRC8.start()
    CRC8.message_queue = {"good_test" : False}
        

    # L1.E4 - Ajouter l'initialisation des pattes d'entrée et de l'horloge
    await init.initReset(dut)

    # Driver and Sink for the dut UART RX/TX channels
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    message_queue = cocotb.queue.Queue()
    # L1.E4 - Start thread for the reply function for the expected UART response.
    for i in range(2):
        i = i + 1
        Thread_uart = cocotb.start_soon(coro=wait_reply(dut, uart_sink, message_queue,CRC8.message_queue))
        # Send read command
        value = int(random.randint(0, 0xFFFFFFFF))
        reg9 = uv.build_command_message(uv.Command.READ.value, 0x9, 0x0 + value)
        print(f"[DEBUG] Loop {i+1} ------------------------")
        print(f"[DEBUG] Loop {i+1}: Sending command {hex(reg9)}")
        await uart_driver.write(reg9.buff)
        await uart_driver.wait()

        # Send CRC
        crc8 = uv.get_expected_crc(reg9.buff)
        if(i == 2):
            CRC8.message_queue = {"good_test" : False}
            print(f"[DEBUG] CRC : {bin(crc8)}")
            #crc8 = crc8 ^ 0xFFFF
            crc8 =+ 1
            print(f"[DEBUG] CRC : {bin(crc8)}")
        crc8bin = cocotb.binary.BinaryValue(value=crc8, n_bits=8, bigEndian=False)
        await uart_driver.write(crc8bin.buff)
        await uart_driver.wait()


        # Wait for response to complete or for timeout
        packetSplitter = await Thread_uart
        if packetSplitter is None:
            print(f"[DEBUG] Loop {i+1}: Received response None")
            break
        print(f"[DEBUG] Loop {i+1}: Received response {hex(int(packetSplitter))}")
        message, crc = await message_queue.get()
        
        
        # print(f"[LOOP END] -- data: 0x{message} -- crc: 0x{crc}")
        # print(f"[LOOP END] -- data: {message} -- crc: {crc}")
       

    print("ici on a fini cool")


async def wait_reply(dut, uart_sink, message_queue,message_queue2):
    # Non-infinite wait loop. Throw cocotb exception if timeout is reached (to do)
    for x in range(0, 100):
        if uart_sink.count() >= 7:  # 6 octets du message + le CRC
            break
        await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

    if x == 99:
        print("Timeout")
        logger = SimLog("cocotb.Test")
        logger.info("Timeout for wait reply")
        print(message_queue2['good_test'])
        if message_queue2["good_test"] == False:
            print("ist normal to crash the crc was not good")
        else:
            raise RuntimeError("Timeout for wait reply")
        # await message_queue.put(None)
        return None
    else:
        message_bytes = bytes(await uart_sink.read(count=6))
        crc_bytes = bytes(await uart_sink.read(count=1))
        message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
        crc = cocotb.binary.BinaryValue(value=crc_bytes, n_bits=8, bigEndian=False)
        print("After a wait of " + str(x) + "000 clocks, received message: ")
        print("MESSAGE : 0x{0:0{width}x}".format(message.integer, width=12))
        print("CRC     : 0x{0:0{width}x}".format(crc.integer, width=12))
        print(f"[DEBUG] message type : {type(message)}")
        await message_queue.put((message, crc_bytes))
        return message
    