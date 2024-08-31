import cocotb
from cocotb.clock import Clock
import os
import pydevd_pycharm


# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def do_wait_only(dut):
    print("[DEBUG] Starting test_do_wait_only")
    PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')
    print(PYCHARMDEBUG)
    if(PYCHARMDEBUG == "enabled"):
        pydevd_pycharm.settrace('localhost', port=53333, stdoutToServer=True, stderrToServer=True)
        print("[DEBUG] PYCHARM DEBUG ENABLED\n")

    # set a signal to some value
    dut.reset.value = 1

    # fetch value from a signal in the dut
    fetch_value = dut.reset.value

    # Confirm type of read signal. Expected: cocotb.binary.BinaryValue
    print(type(fetch_value))

    # start a clock signal
    await cocotb.start(Clock(dut.clk, 10, units='ns').start())

    # wait for 1000 clock periods triggers every rising edge
    await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

