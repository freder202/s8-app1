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
from enum import Enum
import utilsVerif as uv

from MMC_TEMPLATE import * 

#In this case dut is (starting from top) : dut.inst_packet_merger.inst_crc_calc
# FROM : /gei815-amorce-problematique/design/digital/shared/CRC8_gei816.sv
# module CRC8816 #(parameter
#     DATA_LENGTH = 32,
#     DATA_LENGTH_BYTES = (DATA_LENGTH/8))(
#     input logic clk,
#     input logic reset,
#     input logic i_valid,
#     input logic i_last,
#     input logic [7:0] i_data,
#     output logic o_match,
#     output logic o_done,
#     output logic [7:0] o_crc8
#     );

class MMC_CRC8(MMC_TEMPLATE):
    
    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.input_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.i_valid,
            datas=dict(SigInA=self.dut.i_data, SigInB=self.dut.i_last, SigModeleOut=self.dut.o_crc8),
            Name="InputMonitor"
        )
        self.output_mon = DataValidMonitor_Template(
            clk=self.dut.clk,
            valid=self.dut.o_done,
            datas=dict(SigOutA=self.dut.o_match, SigOutB=self.dut.o_done, ),
            Name="OutputMonitor"
        )

    def model(self, InputsA: List[int], InputsB: List[int]) -> List[int]:
    # equivalent model to HDL code
        # print("[MMC_CRC8 CLASS] we are in model")
        print(InputsA)
        print(InputsB)
        
        isModelValid = False
        crc = uv.get_expected_crc(InputsA)
        print(f"[MMC_CRC8 CLASS --  model] Crc modele :{hex(crc)}")
        print(f"[MMC_CRC8 CLASS --  model] Crc from SystemVeriloft :{hex(InputsB[0])}")

        if(crc == InputsB[0]):
            isModelValid = True

        return isModelValid


    async def _checker(self) -> None:
        # print("[MMC_CRC8 CLASS] Checker have been triggered!")
        #init variable
        iLastVar = False
        oLastVar = False
        TestDone = False

        #isSubTestDone = True
        testCounter = 0

        modeleData = []
        
        class isSubTestDone(Enum):
            WAITING_TO_START = 0
            DOING = 1
            TEST_DONE = 2

        test_state = isSubTestDone.WAITING_TO_START

        while True:
            ##############################DO NOT DELETE##################################
            # GIVE AT LEAST 1 CLOCK CYCLE THE GODDAM WHOLE TEST CRASH WITHOUT THIS
            await cocotb.triggers.ClockCycles(self.dut.clk, 1000, rising=True)
            ##############################DO NOT DELETE##################################

            if(test_state == isSubTestDone.TEST_DONE):
                #print(f"[MMC_CRC8 CLASS] test_state {test_state}")
                testCounter += 1
                iLastVar = False
                oLastVar = False
                TestDone = False
                test_state = isSubTestDone.WAITING_TO_START
                modeleData = []
                #print(f"[MMC_CRC8 CLASS] test_state {test_state}")


            if (test_state == isSubTestDone.WAITING_TO_START):
                print(f"[MMC_CRC8 CLASS] Debut test #{testCounter}")
                test_state = isSubTestDone.DOING

            #else : #test_state == isSubTestDone.DOING
            #    pass 

            if(TestDone == False):
                #lab2E1 : wait until queue is full
                inqsize = self.input_mon.values.qsize()
                if(inqsize != 0):
                    #print(inqsize)
                    pass
                if(inqsize == 7):
                    while(self.input_mon.values.empty() != True):
                        inval = await self.input_mon.values.get()
                        modeleData.append(inval)
                        print(inval)
                        if(int(inval["SigInB"]) == 1):
                            # print(f"[MMC_CRC8 CLASS] {modeleData}")
                            
                            les_6_premier_sigInA = []
                            out_crc8 = []

                            for x in modeleData:
                                if(len(les_6_premier_sigInA) < 6):
                                    #print(f"[MMC_CRC8 CLASS----] {hex(int(x['SigInA']))}")
                                    les_6_premier_sigInA.append(int(x["SigInA"]))
                                    
                                else:
                                    #print(f"[MMC_CRC8 CLASS ----] {hex(int(x['SigModeleOut']))}")
                                    out_crc8.append(int(x["SigModeleOut"]))
                                    break

                            modeleResult = self.model(les_6_premier_sigInA, out_crc8)
                            iLastVar = True
                            
                    pass

                outqsize = self.output_mon.values.qsize()
                if(outqsize != 0):
                    print(f"Outqsize = {outqsize}")
                    outval = await self.output_mon.values.get()
                    if(int(outval["SigOutB"]) == 1):
                        oLastVar = True

                if( (iLastVar == True) and (oLastVar == True)):
                    #assert pour modele
                    print(f"[MMC_CRC8 CLASS -- Assertion] Modele = {modeleResult}")
                    #assert pour checker
                    if(int(outval["SigOutA"]) == 1):
                        print("[MMC_CRC8 CLASS -- Assertion] o_match == TRUE")
                        assert True
                    else:
                        assert False

                    test_state = isSubTestDone.TEST_DONE
                    TestDone = True
