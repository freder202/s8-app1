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

from MMC_TEMPLATE import *

# inst_tdc_channel_0(
#         # .reset(reset),
#         # .clk(clk),
#         # .i_trigger(sipms[0]),
#         # .i_enable_channel(TDC_en_if.enable_channels[0]),
#         # .i_clear(tdc1_if.clear),
#         # .o_busy(s_busy[0]),
#         # .o_hasEvent(tdc1_if.hasEvent),
#         # .o_chanID(tdc1_if.chan),
#         # .o_timestamp(tdc1_if.timestamp),
#         # .o_pulseWidth(tdc1_if.timeOverThreshold)
# );

#In this case dut is (starting from top) : dut.inst_packet_merger.inst_crc_calc
class MMC_TDC(MMC_TEMPLATE):
   
    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.input_mon = DataValidMonitor_Template(
            clk=self.dut.clk, # should this me the inst_tdc_channel_0 clk ?
            valid=self.dut.inst_tdc_channel_0.reset,
            datas=dict(
             SigInA=self.dut.inst_tdc_channel_0.i_trigger, 
             SigInB=self.dut.inst_tdc_channel_0.i_clear
             ),
            Name="InputMonitor"
        )
        self.output_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.inst_tdc_channel_0.o_hasEvent,
            datas=dict(
             SigOutA=self.dut.inst_tdc_channel_0.o_busy,
             sigOutB=self.dut.inst_tdc_channel_0.o_chanID,
             SigOutC=self.dut.inst_tdc_channel_0.o_timestamp,
             SigOutD=self.dut.inst_tdc_channel_0.o_pulseWidth
             ),
            Name="OutputMonitor"
        )

        def model(self, InputsA: List[int], InputsB: List[int]) -> List[int]:
        # equivalent model to HDL code # TODO FAIRE UN VRAI MODELE CRC8
            model_result1 = 0
            model_result2 = 1
            return [model_result1, model_result2]
            

    async def _checker(self) -> None:
        print("[MMC_TDC CLASS] Checker have been triggered!")

        #init variable
        iLastVar = False
        oLastVar = False
        TestDone = False


        print("poil")

        # #TODO COLLECT DATA FROM int(inval["SigInA"]) and input it in a model then assert CRC
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
                if(inqsize == 18):
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
