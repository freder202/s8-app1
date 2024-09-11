import cocotb
from cocotb.clock import Clock
import os
import pydevd_pycharm
from cocotb.triggers import Join
from cocotbext.uart import UartSource, UartSink
from utilsVerif import print_cocotb_BinaryValue
from cocotb.log import SimLog


def initDebug():
    print(f"[DEBUG] Starting {__file__}"      )
    PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')
    print(PYCHARMDEBUG)
    if (PYCHARMDEBUG == "enabled"):
        pydevd_pycharm.settrace('localhost', port=53333, stdoutToServer=True, stderrToServer=True)
        print("[DEBUG] PYCHARM DEBUG ENABLED\n")
    pass

async def initReset(dut):

    #Preset all top inputs, from spec sheet : reset, clk, clkMHz, in_sig, resetCyclic, sipms[1:0]
    dut.reset.value         = 1
    dut.clk.value           = 0
    dut.clkMHz.value        = 1
    dut.in_sig.value        = 1
    dut.resetCyclic.value   = 1
    dut.sipms[0].value      = 0
    dut.sipms[1].value      = 1

    # Confirm type of read signal. Expected: cocotb.binary.BinaryValue
    print(f"[DEBUG] reset.value type : {type(dut.reset.value)}")
    print(f"[DEBUG] clk.value type : {type(dut.clk.value)}")
    print(f"[DEBUG] in_sig.value type : {type(dut.in_sig.value)}")
    print(f"[DEBUG] resetCyclic.value type : {type(dut.resetCyclic.value)}")
    print(f"[DEBUG] sipms.value type : {type(dut.sipms.value)}")

    # start a clock signal
    await cocotb.start(Clock(dut.clk, 10, units='ns').start())

    # wait for 10 clock periods triggers every rising edge
    await cocotb.triggers.ClockCycles(dut.clk, 10, rising=True)

    # disable reset
    dut.reset.value = 0
    await cocotb.triggers.ClockCycles(dut.clk, 1, rising=True)

    dut.in_sig.value = 0
    await cocotb.triggers.ClockCycles(dut.clk, 1, rising=True)

    print("[DEBUG] INIT DONE!")

    pass

# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def lab1E2(dut):

    initDebug()
    await initReset(dut)

    print("[DEBUG] Prepping uart...")
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    # Send arbitrary value, then wait for transaction to complete
    SomeValue = cocotb.binary.BinaryValue(value=0x1023456789ABDCEF, n_bits=64, bigEndian=False)
    await uart_driver.write(SomeValue.buff)
    await uart_driver.wait()

    pass



