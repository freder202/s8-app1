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
        self.message_queue = cocotb.queue.Queue()
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
             SigOutA=self.dut.inst_tdc_channel_0.o_hasEvent,
             SigOutB=self.dut.inst_tdc_channel_0.o_busy,
             SigOutC=self.dut.inst_tdc_channel_0.o_chanID,
             SigOutD=self.dut.inst_tdc_channel_0.o_timestamp,
             SigOutE=self.dut.inst_tdc_channel_0.o_pulseWidth
             ),
            Name="OutputMonitor"
        )


    def _convert_message_queue_to_ps(self,time_fred):
        if time_fred[1] == 'ns':
            return time_fred[0] * 1000
        elif time_fred[1] == 'us':
            return time_fred[0] * 1000000
        elif time_fred[1] == 'ms':
            return time_fred[0] * 1000000000
        elif time_fred[1] == 'ps':
            return time_fred[0] * 1
        else:
            return 0

    def model(self, InputsA: List[int], InputsB: List[int]) -> List[int]:
        test_time_as_ps = self._convert_message_queue_to_ps(self.message_queue['time_tested'])
        is_pulse_width_valid = ((test_time_as_ps // 40 ) == int(InputsB['SigOutE'])) 
        is_pulse_width_valid = is_pulse_width_valid and (int(InputsB['SigOutE']) < 125001) # 125000 is the maximum value of the counter
        print(f"expected: {test_time_as_ps // 40}count -> |{test_time_as_ps /( 1 * 1000 * 1000)}us | test result: {int(InputsB['SigOutE']) } count -> | [{(int(InputsB['SigOutE']) * 40) -20 } ps and {(int(InputsB['SigOutE']) * 40) +20 }ps]")

        return [is_pulse_width_valid]
            

    async def _checker(self) -> None:
        print("[MMC_TDC CLASS] Checker have been triggered!")

        iLastVar = False
        oLastVar = False
        TestDone = False
        testCounter = 0
        
        class isSubTestDone(Enum):
            WAITING_TO_START = 0
            DOING = 1
            TEST_DONE = 2

        test_state = isSubTestDone.WAITING_TO_START

        # #TODO COLLECT DATA FROM int(inval["SigInA"]) and input it in a model then assert CRC
        while True:
            ##############################DO NOT DELETE##################################
            # GIVE AT LEAST 1 CLOCK CYCLE THE GODDAM WHOLE TEST CRASH WITHOUT THIS
            await cocotb.triggers.ClockCycles(self.dut.clk, 100, rising=True)
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
                print(f"[MMC_TDC CLASS] Debut test #{testCounter}")
                test_state = isSubTestDone.DOING

            if(TestDone == False):
                outqsize = self.output_mon.values.qsize()
                if(outqsize > 1):
                    print("stu ici le magasin de variables ?")
                    # print(f"Outqsize = {outqsize}")
                    outval = await self.output_mon.values.get()
                    if outval["SigOutA"] == 0:
                        print("on est pas pret (toute les donnees du output mon ne sont pas la)")
                        continue
                    else:
                        assert outval["SigOutA"] == 1 # o_hasEvent 
                        inval = await self.input_mon.values.get()
                        print("on est pret (toute les donnees du output mon sont la)")
                        is_pulse_width_valid =  self.model(inval,outval)
                        
                        if 'interpolation_time' in self.message_queue and  self.message_queue['interpolation_time'] > 2200:
                            print("interpolation time failed!!!!!! \n\n\n\n\n\n\n\n")
                            assert False
                        
                        if not is_pulse_width_valid:
                            break
                        assert is_pulse_width_valid
                        
                        TestDone = True
                        test_state = isSubTestDone.TEST_DONE
                        self.input_mon.values.empty()
                        self.output_mon.values.empty()
                        
            else:
                if(self.message_queue['isTestSupposedToFail']):
                    assert False