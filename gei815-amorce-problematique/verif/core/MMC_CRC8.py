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
            datas=dict(SigInI_DATA=self.dut.i_data, SigInI_LAST=self.dut.i_last),
            Name="InputMonitor"
        )
        self.output_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.o_done,
            datas=dict(SigOutO_MATCH=self.dut.o_match, SigOutO_DONE=self.dut.o_done),
            Name="OutputMonitor"
        )

    def model(self, InputsA: List[int], InputsB: List[int]) -> List[int]:
    # equivalent model to HDL code
        print("we are in the model")
        print(InputsA)
        print(InputsB)
        model_result1 = 0
        model_result2 = 1
        return [model_result1, model_result2]


    async def _checker(self) -> None:
        print("[MMC_CRC8 CLASS] Checker have been triggered!")
        #init variable
        iLastVar = False
        oLastVar = False
        isTestDone = False

        # GIVE AT LEAST 1 CLOCK CYCLE THE GODDAM WHOLE TEST CRASH WITHOUT THIS        
        await cocotb.triggers.ClockCycles(self.dut.clk, 100, rising=True)

        print(self.input_mon.values.qsize())

        ##############################DO NOT DELETE##################################
        while(isTestDone == False):
            #lab2E1 : wait until queue is full
            if(self.input_mon.values.qsize() != 0):
                #print(inqsize)
                pass
            if(self.input_mon.values.qsize() >= 7):
                print("WE HAVE ENOUGH VALUE FOR THE TEST")
                while(self.input_mon.values.empty() != True):
                    inval = await self.input_mon.values.get()
                    print(inval)
                    if(int(inval["SigInI_LAST"]) == 1):
                        iLastVar = True
                # inqsize.empty()
                isTestDone = True

        outqsize = self.output_mon.values.qsize()
        if(outqsize != 0):
            print(f"Outqsize = {outqsize}")
            outval = await self.output_mon.values.get()
            if(int(outval["SigOutO_DONE"]) == 1):
                oLastVar = True

        if( (iLastVar == True) and (oLastVar == True)):
            if(int(outval["SigOutO_MATCH"]) == 1):
                print("o_match == TRUE")
                assert True
            else:
                assert False
                
            
        expected_inputs = await self.input_mon.values.get()
        actual = await self.output_mon.values.get()
        print(f"Actual : {actual}")
        print(f"Expected : {expected_inputs}")
        
        #     expected = self.model(InputsA=expected_inputs["SigInA"], InputsB=expected_inputs["SigInB"]
        #     )

        #     # compare expected with actual using assertions. Exact indexing must
        #     # be adapted to specific case and model return value
        #     # assert actual["SigOutA"] == expected[0]
        #     # assert actual["SigOutB"] == expected[1]
        #     assert True



            # assert False running this might cause error
            
