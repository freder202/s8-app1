# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0

# adapted from https://github.com/cocotb/cocotb/blob/stable/1.9/examples/matrix_multiplier/tests/test_matrix_multiplier.py

from typing import Any, Dict, List

import cocotb
from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.handle import SimHandleBase
from cocotb.queue import Queue
from cocotb.runner import get_runner
from cocotb.triggers import RisingEdge
from cocotb.log import SimLog

class DataValidMonitor_Template:
    """
    Reusable Monitor of one-way control flow (data/valid) streaming data interface

    Args
        clk: clock signal
        valid: control signal noting a transaction occured
        datas: named handles to be sampled when transaction occurs
    """
        # this dont need to change from template to template (FB) 
    def __init__(self, clk: SimHandleBase, valid: SimHandleBase, datas: Dict[str, SimHandleBase], Name:str = "Stock Name"):
        self.values = Queue[Dict[str, int]]()
        self._clk = clk
        self._datas = datas
        self._valid = valid
        self._coro = None # is monitor running? False if "None"
        self.Name = Name
        self.log = SimLog("cocotb.Monitor.%s" % (type(self).__qualname__))

        # this dont need to change from template to template (FB) 
    def start(self) -> None:
        """Start monitor"""
        if self._coro is not None:
            raise RuntimeError("Monitor already started")
        self._coro = cocotb.start_soon(self._run())

        # this dont need to change from template to template (FB) 
    def stop(self) -> None:
        """Stop monitor"""
        if self._coro is None:
            raise RuntimeError("Monitor never started")
        self._coro.kill()
        self._coro = None

        # this dont need to change from template to template (FB)
    async def _run(self) -> None:
        while True:
            await RisingEdge(self._clk)
            # this condition decides when to record the signal states
            if self._valid.value.binstr != "1":
                # wait until valid is asserted, instead of checking every clock cycle.
                await RisingEdge(self._valid)
                # skip whatever comes after, and start the while loop again
                continue
            # store the samples, as formatted by the _sample method
            self.values.put_nowait(self._sample())

        # this dont need to change from template to template (FB)
    def _sample(self) -> Dict[str, Any]:
        """
        Samples the data signals and builds a transaction object

        Return value is what is stored in queue. Meant to be overriden by the user.
        """
        # possible messages to test monitor
        self.log.info(f"[{self.Name}] Data sampled!")
        # self.log.info({name: handle.value for name, handle in self._datas.items()})


        # # for loop going through all the values in the signals to sample (see constructor)
        return {name: handle.value for name, handle in self._datas.items()}

#In this case dut is (starting from top) : dut.inst_packet_merger.inst_crc_calc
class MMC_TEMPLATE(object):

    def start(self) -> None:
        """Starts monitors, model, and checker coroutine"""
        if self._checkercoro is not None:
            raise RuntimeError("Monitor already started")
        self.input_mon.start()
        self.output_mon.start()
        
        self._checkercoro = cocotb.start_soon(self._checker())

    def stop(self) -> None:
        """Stops everything"""
        if self._checkercoro is None:
            raise RuntimeError("Monitor never started")
        self.input_mon.stop()
        self.output_mon.stop()
        self._checkercoro.kill()
        self._checkercoro = None

    # abstract methode to be implemented in the child class 
    def __init__(self, logicblock_instance: SimHandleBase):
        self.dut = logicblock_instance
        self._checkercoro = None
        self.log = SimLog("[SIMLOG] cocotb.MMC.%s" % (type(self).__qualname__))
        print("[MMC_TDC] Class instantiated")

    
    # abstract methode to be implemented in the child class
    def model(self, InputsA: List[int], InputsB: List[int]) -> List[int]:
        raise NotImplementedError()
        # # equivalent model to HDL code
        # model_result1 = 0
        # model_result2 = 1
        # return [model_result1, model_result2]

    # abstract methode to be implemented in the child class
    async def _checker(self) -> None:
        raise NotImplementedError()