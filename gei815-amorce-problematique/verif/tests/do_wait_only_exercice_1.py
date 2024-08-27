import cocotb
from cocotb.clock import Clock

import os

import pydevd_pycharm
import cocotbext_uart_demo


# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def do_wait_only_exercice_1(dut):
    print("Starting test_do_wait_only")

    PYCHARMDEBUG = os.environ.get('PYCHARMDEBUG')

    print(PYCHARMDEBUG)

    if(PYCHARMDEBUG == "enabled"):
        pydevd_pycharm.settrace('localhost', port=53333, stdoutToServer=True, stderrToServer=True)

    # set a signal to some value
    dut.reset.value = 1

    dut.in_sig.value = 1
    dut.resetCyclic.value = 1

    dut.sipms.value = 3
    # fetch value from a signal in the dut
    fetch_value = dut.reset.value

    # Confirm type of read signal. Expected: cocotb.binary.BinaryValue
    print(type(fetch_value))

    await cocotb.start(Clock(dut.clk, 10, units='ns').start())

    # wait for 1000 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 10, rising=True)

    dut.reset.value = 0
    await cocotb.triggers.ClockCycles(dut.clk, 1, rising=True)

    # wait for 1000 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 100, rising=True)