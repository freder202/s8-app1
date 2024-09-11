import cocotb
from cocotb.clock import Clock
import os
import pydevd_pycharm
from cocotb.triggers import Join
from cocotbext.uart import UartSource, UartSink
from utilsVerif import print_cocotb_BinaryValue
from cocotb.log import SimLog
import MMC_TDC as MMC


def initDebug():
    print("[DEBUG] Starting X_TDC")
    PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')
    print(PYCHARMDEBUG)
    if (PYCHARMDEBUG == "enabled"):
        pydevd_pycharm.settrace('localhost', port=53333, stdoutToServer=True, stderrToServer=True)
        print("[DEBUG] PYCHARM DEBUG ENABLED\n")
    pass

async def initReset(dut):
    dut.reset.value = 1
    dut.clk.value = 0
    dut.i_trigger = 0
    dut.i_enable_channel = 0
    dut.i_clear = 0
    dut.o_busy = 0
    dut.o_hasEvent = 0
    dut.o_chanID = 0
    dut.o_timestamp = 0x0
    dut.o_pulseWidth = 0x0

    # start a 100 MHz clock signal 
    await cocotb.start(Clock(dut.clk, 10, units='ns').start())

    # wait for 10 clock periods triggers every rising edge
    await cocotb.triggers.ClockCycles(dut.clk, 10, rising=True)

    # disable reset
    dut.reset.value = 0
    await cocotb.triggers.ClockCycles(dut.clk, 1, rising=True)

    await cocotb.triggers.ClockCycles(dut.clk, 1, rising=True)

    print("[DEBUG] INIT DONE!")

    pass

# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def X_TDC(dut):

    initDebug()
    await initReset(dut)

    TDC = MMC.MMC_TDC(dut.ins)

    # print("[DEBUG] Prepping uart...")
    # uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    # uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    # # Send arbitrary value, then wait for transaction to complete
    # SomeValue = cocotb.binary.BinaryValue(value=0x1023456789ABDCEF, n_bits=64, bigEndian=False)
    # await uart_driver.write(SomeValue.buff)
    # await uart_driver.wait()

    pass



