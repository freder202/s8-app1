#!/usr/bin/env python3


## Standard Packages
from sys import exit

import argparse
import os
from os.path import isfile



def CheckCocotbInstall():

    import importlib.util

    spam_spec = importlib.util.find_spec("cocotb")
    found = spam_spec is not None
    if(found != True):
        print("Cocotb not found")
        exit(1)

    spam_spec = importlib.util.find_spec("cocotb_bus")
    found = spam_spec is not None
    if(found != True):
        print("Cocotb not found")
        exit(1)

    spam_spec = importlib.util.find_spec("cocotb_test")
    found = spam_spec is not None
    if(found != True):
        print("Cocotb not found")
        exit(1)

    spam_spec = importlib.util.find_spec("cocotbext.uart")
    found = spam_spec is not None
    if(found != True):
        print("cocotbext.uart not found")
        exit(1)

    import cocotb
    import cocotb_bus
    import cocotb_test
    import cocotbext


    if(cocotb.__version__ != "1.9.0"):
        print("Wrong Cocotb version, found version " + cocotb.__version__ + " and expecting 1.6.2")
        exit(1)
    elif(cocotb_bus.__version__ != "0.2.1"):
        print("Wrong Cocotb_bus version, found version " + cocotb_bus.__version__ + " and expecting 0.2.1")
        exit(1)
    elif(cocotb_test.__version__ != "0.2.5"):
        print("Wrong Cocotb_test version,  found version " + cocotb_test.__version__ + " and expecting 0.2.1")
        exit(1)
    # no version number in module, skip.
    #elif(cocotbext.verson.__version__ != "0.1.2"):
    #    print("Wrong Cocotbext.uart version")
    #    exit(1)

    print("cocotb packages ok.")
    #exit()



CheckCocotbInstall()

parser = argparse.ArgumentParser(description='Verification environment for cocotb and VManager.')

# texte
parser.add_argument('-t', '--test', type=str, default="do_wait_only", help='String. Test name. See $VERIF_ROOT/tests for list.')
parser.add_argument('-d', '--testdir', type=str, default="tests", help='String. Specify test subdirectory, defaults to $VERIF_ROOT/tests.')

# int
parser.add_argument('--seed', type=str, help='String. Random seed. Accepts "random" or integer. Defaults to "random" if empty')

# bool
parser.add_argument('-w', '--waves', dest='waves', help="Bool Switch. Save waveforms to disk, default is false.", action='store_true') #action="store_true"
parser.set_defaults(waves=None)

parser.add_argument('-b', '--batch', help="Bool Switch. Batch mode, no gui", action="store_true")
parser.add_argument('--sva', help="Bool Switch. Include SystemVerilog Assertions bindings.", action="store_true")
parser.add_argument('-c', '--cov', help="Bool Switch. Enable functional coverage collection.", action="store_true")
parser.add_argument('--cocotb-sanity-check', dest='cocotbsanity', help="Bool Switch. Run cocotb sanity check.", action="store_true")
parser.add_argument('-p', '--pycharm-debug', dest='pydebug', help="Bool Switch. Enable Python interactive debug or not.", action="store_true")


# parser.add_argument('integers', metavar='N', type=int, nargs='+',
#                     help='an integer for the accumulator')

args = parser.parse_args()
print(args.waves)


PROJECT_ROOT = os.environ.get('PROJECT_ROOT')
PWD = os.environ.get('PWD')
SIM = os.environ.get('SIM')
HOME = os.environ.get('HOME')
VERIF_ROOT = os.environ.get('VERIF_ROOT')
DESIGN_ROOT = os.environ.get('DESIGN_ROOT')
MODELS_HLM_ROOT = os.environ.get('MODELS_HLM_ROOT')
DUT_INST_NAME = os.environ.get('DUT_INST_NAME')

VMANAGER_REGRESSIONS_AREA = os.environ.get('VMANAGER_REGRESSIONS_AREA')


if(args.pydebug == True):
    os.environ["PYCHARMDEBUG"] = "enabled"


if not isfile(PROJECT_ROOT + "/.hosts_local"):
    print("Licence redirection file for vmanager missing. Please recover from the git repository.")
    print(PROJECT_ROOT + "/.hosts_local")
    exit(1)


if (PROJECT_ROOT == None):
    print("No SVE environment found.")
    exit(1)

if(PWD == PROJECT_ROOT):
    print("Running sims from working copy root is possible but not ")
    print("recommended. moving de default simulation directory")
    print("Currently in " + os.getcwd())
    os.chdir(PROJECT_ROOT + "/simdir")
    print("Now in " + os.getcwd())

if(PWD == HOME):
    print("Running sims from the user's home directory is possible")
    print("but not recommended. Please run from other directory")
    exit(1)


if(PWD != (PROJECT_ROOT + "/simdir")) and (VMANAGER_REGRESSIONS_AREA not in PWD):
    print("For development, coherce simulation directory")
    print("Please use   " + PROJECT_ROOT + "/simdir")
    print("or disable checker in script.")
    print("Currently in " + os.getcwd())
    os.chdir(PROJECT_ROOT + "/simdir")
    print("Now in " + os.getcwd())



# Set default manifest files
DesignFiles="-f " + DESIGN_ROOT + "/digital/digital_design_manifest.f"
Models= "-f " + MODELS_HLM_ROOT + "/mixed_sig_modules_manifest.f"

# simvision command for waveforms.
# 		default saves all signals in design
WavesScript=VERIF_ROOT + "/scripts/waves.tcl"

# Coverage switches

CoverageCommands = ""
if(args.cov == True):
    CoverageCommands =  " -coverage u" # code and functional coverage. ICC user guide. Also activates cover properties, so no need for -abvcoveron
    CoverageCommands += " -covfile " + VERIF_ROOT + "/scripts/coverage.tcl"
    CoverageCommands += " -covdut " + DUT_INST_NAME 	## will not capture coverage from the testbench...
    CoverageCommands += " -covoverwrite"
    CoverageCommands += " -covtest " + args.test

# Main xrun switches
# 		VHDL '93 support, -v200x also possible
MainOptions  = "-v93"
MainOptions += " -rnm_package" ## real number modeling for SystemVerilog

#set MainOptions="$MainOptions "
MainOptions += " -nowarn COVFHT"
MainOptions += " -nowarn COVCGN"
MainOptions += " -nowarn COVUTA"
MainOptions += " -nowarn ICFCLD"
MainOptions += " -nowarn WSEM2009"

if SIM == "xcellium":
    MainOptions += " -no_analogsolver"


# print out the random seed in the log file to help rerun in case of error
MainOptions= MainOptions + " -input " + VERIF_ROOT + "/scripts/misc_commands.tcl"

# optional arguments
if(args.batch == False):
    MainOptions += " -gui"
    if(args.waves == None):
        print("Gui mode without waveform specification, turn waves on")
        args.waves = True


if(args.batch == True):
    MainOptions += " -run -exit"
    if(args.waves == None):
        print("batch mode without waveform specification, turn waves off")
        args.waves = False

if(args.waves == True):
    # access and +rwc switches taken core of by cocotb
    MainOptions += " -input " + WavesScript

AssertionFiles = ""
if(args.sva == True):
    AssertionFiles += "-f " + VERIF_ROOT + "/tb_sva_bindings.f"


## Default: do nothing. Note: can also use -svseed, seems to change something for reporting in log...
if(args.seed == None):
    MainOptions += " -seed random"
else:
    MainOptions += (" -seed " + args.seed)


# Method 2 Use cocotb_test with force to true
# seems to print stdout to stderr

from cocotb_test.simulator import run
import os

def test_dff():
    run(
        verilog_sources=[os.path.join(VERIF_ROOT, "core", "cocotb_sanitycheck", "dff.sv")],
        force_compile = True,
        sim_args=[MainOptions],
        python_search=[os.path.join(VERIF_ROOT, "core", "cocotb_sanitycheck")],
        toplevel="dff_test",            # top level HDL
        testcase="test_dff_simple",
        module="dff_cocotb"        # name of cocotb test module
    )

def test_start():
    print(DesignFiles)
    run(
        verilog_sources=[],
        force_compile = True, # fixes leaving verilog_sources empty
        compile_args=[DesignFiles, Models, AssertionFiles, CoverageCommands],
        sim_args=[MainOptions, CoverageCommands],
        python_search=[os.path.join(VERIF_ROOT, "tests")],
        toplevel="top",            # top level HDL
        testcase=args.test,
        module=args.test        # name of cocotb test module
    )

if args.cocotbsanity == True:
    test_dff()
else:
    test_start()
