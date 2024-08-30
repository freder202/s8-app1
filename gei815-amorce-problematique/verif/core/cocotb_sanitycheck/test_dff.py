from cocotb_test.simulator import run
import pytest
import os

tests_dir = os.path.dirname(__file__)

def test_dff():
    run(
        verilog_sources=[os.path.join(tests_dir, "dff.sv")],
        toplevel="dff_test",            # top level HDL
        module="dff_cocotb"        # name of cocotb test module
    )


if __name__ == "__main__":
    test_dff()
    # test_dff_vhdl()