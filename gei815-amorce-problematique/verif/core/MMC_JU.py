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

    def __init__(
        self, clk: SimHandleBase, valid: SimHandleBase,
        datas: Dict[str, SimHandleBase], Name:str = "Stock Name"
    ):
        self.values = Queue[Dict[str, int]]()
        self._clk = clk
        self._datas = datas
        self._valid = valid
        self._coro = None # is monitor running? False if "None"

        self.Name = Name

        self.log = SimLog("cocotb.Monitor.%s" % (type(self).__qualname__))

    def start(self) -> None:
        """Start monitor"""
        if self._coro is not None:
            raise RuntimeError("Monitor already started")
        self._coro = cocotb.start_soon(self._run())

    def stop(self) -> None:
        """Stop monitor"""
        if self._coro is None:
            raise RuntimeError("Monitor never started")
        self._coro.kill()
        self._coro = None


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

    def _sample(self) -> Dict[str, Any]:
        """
        Samples the data signals and builds a transaction object

        Return value is what is stored in queue. Meant to be overriden by the user.
        """
        # possible messages to test monitor
        self.log.info(f"[{self.Name}] Data sampled!")
        #self.log.info({name: handle.value for name, handle in self._datas.items()})


        # for loop going through all the values in the signals to sample (see constructor)
        return {name: handle.value for name, handle in self._datas.items()}

#In this case dut is (starting from top) : dut.inst_packet_merger.inst_crc_calc
class MMC_CRC8:
    """
    Reusable checker of a checker instance

    Args
        logicblock_instance: handle to an instance of a logic block
    """

    def __init__(self, logicblock_instance: SimHandleBase):
        """
        These data come from design/digital/UART/packet_merger.sv
        CRC8816 #(.DATA_LENGTH(MESSAGE_LENGTH)) inst_crc_calc (
            .clk(clk),
            .reset(crc_clear_r),
            .i_data(s_uart_data),
            .i_valid(s_new_uart_valid),
            .i_last(crc_last_r),
            .o_match(s_crc_match),
            .o_done(s_crc_done)
            );
        """

        self.dut = logicblock_instance

        self.input_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            # Having "1" on valid pin tells the monitor to records
            # what's on datas variable through _sample()
            valid=self.dut.i_valid,
            datas=dict(SigInA=self.dut.i_data, SigInB=self.dut.i_last),
            Name="InputMonitor"
        )

        self.output_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.o_done,
            datas=dict(SigOutA=self.dut.o_match, SigOutB=self.dut.o_done),
            Name="OutputMonitor"
        )

        self._checkercoro = None

        self.log = SimLog("[SIMLOG] cocotb.MMC.%s" % (type(self).__qualname__))

        print("[MMC_CRC8] Class instantiated")

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

    """
    The model is supposed to be used in _checker() to compares the results from the monitors
    and it's own value. Every model is unique to it's test and must be created from scratch everytime.
    In this specific case, it should be a CRC calculator.
    """
    def model(self, InputsA: List[int], InputsB: List[int]) -> List[int]:
        # equivalent model to HDL code
        model_result1 = 0
        model_result2 = 1
        return [model_result1, model_result2]


    # Insert logic to decide when to check the model against the HDL result.
    # then compare output monitor result with model result
    # This example might not work every time.

    """
    _checker is asynch
    Called during start()
    must check every monitor trigger with awaits
    must also prep the model
    and must raise exception or asserts to valide the test
    """
    async def _checker(self) -> None:
        print("[MMC_CRC8 CLASS] Checker have been triggered!")

        #init variable
        iLastVar = False
        oLastVar = False
        TestDone = False


        #TODO COLLECT DATA FROM int(inval["SigInA"]) and input it in a model then assert CRC
        while True:
            # dummy await, allows to run without checker implementation and verify monitors
            ##############################DO NOT DELETE##################################
            # GIVE AT LEAST 1 CLOCK CYCLE THE GODDAM WHOLE TEST CRASH WITHOUT THIS
            await cocotb.triggers.ClockCycles(self.dut.clk, 100, rising=True)
            ##############################DO NOT DELETE##################################
            if(TestDone == False):
                #lab2E1 : wait until queue is full
                inqsize = self.input_mon.values.qsize()
                if(inqsize != 0):
                    #print(inqsize)
                    pass
                if(inqsize == 7):
                    while(self.input_mon.values.empty() != True):
                        inval = await self.input_mon.values.get()
                        print(inval)
                        if(int(inval["SigInB"]) == 1):
                            iLastVar = True
                    pass

                outqsize = self.output_mon.values.qsize()
                if(outqsize != 0):
                    print(f"Outqsize = {outqsize}")
                    outval = await self.output_mon.values.get()
                    if(int(outval["SigOutB"]) == 1):
                        oLastVar = True

                if( (iLastVar == True) and (oLastVar == True)):
                    if(int(outval["SigOutA"]) == 1):
                        print("o_match == TRUE")
                        assert True
                    else:
                        assert False

                    TestDone = True
                """
                actual = await self.output_mon.values.get()
                expected_inputs = await self.input_mon.values.get()
                expected = self.model(
                    InputsA=expected_inputs["SignalA"], InputsB=expected_inputs["SignalB"]
                )
    
                # compare expected with actual using assertions. Exact indexing must
                # be adapted to specific case and model return value
                assert actual["SignalC"] == expected[0]
                assert actual["SignalD"] == expected[1]
                """



            # assert False running this might cause error
