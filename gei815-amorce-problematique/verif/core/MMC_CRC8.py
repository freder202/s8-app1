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

#In this case dut is (starting from top) : dut.inst_packet_merger.inst_crc_calc
class MMC_CRC8(MMC_TEMPLATE):
    
    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.input_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
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
            
