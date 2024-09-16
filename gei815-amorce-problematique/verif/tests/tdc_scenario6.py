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
from cocotb.triggers import FallingEdge, RisingEdge
from cocotb.utils import get_sim_time
import MMC_TDC as MMC

import utilsVerif as uv
#Homemade module
import init

import cocotb.simulator

# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def tdc_scenario6(dut):

    init.initDebug("TDC scenario4 - LECTURE REGISTRE SERIAL")

    #FROM design/digital/UART/packet_merger.sv
    TDC = MMC.MMC_TDC(dut)
    TDC.start()
    
    for x in range(0, 2):
            
        time_to_wait = random.randint(50,10000) # ns
        time_to_trigger = random.randint(21,4999) # ns
        
        TDC.message_queue = {'time_tested' : [time_to_trigger,'ns'] ,"isTestSupposedToFail" : False} # 2.5 us

        # L1.E4 - Ajouter l'initialisation des pattes d'entrée et de l'horloge
        await init.initReset(dut)

        # Driver and Sink for the dut UART RX/TX channels
        uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
        uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

        # L1.E4 - Start thread for the reply function for the expected UART response.
        Thread_uart = cocotb.start_soon(coro=t_uart_test(dut, uart_sink))

        # Send read command
        reg9 = uv.build_command_message(uv.Command.WRITE.value, 0x8, 0x01)
        print(f"[DEBUG] {hex(reg9)}")
        await uart_driver.write(reg9.buff)
        await uart_driver.wait()

        # Send CRC
        crc8 = uv.get_expected_crc(reg9.buff)
        crc8bin = cocotb.binary.BinaryValue(value=crc8, n_bits=8, bigEndian=False)
        await uart_driver.write(crc8bin.buff)
        await uart_driver.wait()

        # entropic wait to settle 
        await Timer(time_to_wait,'ns') 

        dut.sipms[0].value = 1
        await Timer(TDC.message_queue["time_tested"][0], TDC.message_queue["time_tested"][1]) # 2.5 us
        dut.sipms[0].value = 0
        
        await FallingEdge(dut.inst_tdc_channel_0.i_trigger)
        timestamp = get_sim_time()
        await RisingEdge(dut.inst_tdc_channel_0.o_hasEvent)
        lautre_timestamp = get_sim_time()
        
        TDC.message_queue['interpolation_time'] = (( lautre_timestamp - timestamp ) // 1000) # ns
        
        print(f" INTERPOLATION TIME :{((lautre_timestamp - timestamp) // 1000)} ns")
        
        
        await Timer(150, 'us')
    print("ici on fail cool")
    Thread_uart.kill()

async def t_uart_test(dut, uart_sink):
    while(True):
        Task_returnMessage = await cocotb.start(wait_reply(dut, uart_sink))

        packetSplitter = await Task_returnMessage
        print(f"[DEBUG] Task_returnMessage type : {type(packetSplitter)}")
        print(packetSplitter)
        print(hex(int(packetSplitter)))
        break;


async def wait_reply(dut, uart_sink):
    for x in range(0, 200):
        if(uart_sink.count() >= 7): ## 6 octets du message + le CRC
            break;
        await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

    if(x == 99):
        print("Timeout")
        logger = SimLog("cocotb.Test")
        logger.info("Timeout for wait reply")
        raise RuntimeError("Timeout for wait reply")
        return None

    else:
        # cocotbext-uart returns byteArray. Convert to bytes first, then to Binary value for uniformity.
        message_bytes = bytes(await uart_sink.read(count=6))
        message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
        # print("After a wait of " + str(x) + "000 clocks, received message: ", end='')
        # print("0x{0:0{width}x}".format(message.integer, width=12))
        # print(f"[DEBUG] message type : {type(message)}")
        return message