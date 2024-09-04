#! /bin/tcsh
########################################################################
## Author  :    Marc-Andre Tetrault
## Project :    Verification Primer
##
## Universite de Sherbrooke
########################################################################
#
# Purpose   :   Parametrize simulation runs
#
########################################################################

# set defaults for switches
set waves=default
set gui=yes
set sva=no
set coverage=no
set randomseed=yes	# change to yes for automatic seed randomization

########################################################################
# LAB1 settings
########################################################################
# set defaults for string variables
setenv LAB_TEST_DUT_NAME test_dut
set test="dut1"
set test_dir="tests"
set assertionfiles=""
set dut="dut"

# Set default manifest files
set DesignFiles="-sv dut.v "
set Models=""
set TestbenchFiles="test_dut.sv"
set assertionfiles="dut_property.sv"


# implication options for lab 1
#set MainOptions="-define no_implication"
set MainOptions="-define implication"
#set MainOptions="-define implication_novac"
########################################################################


# ease temporary file managerement with some restrictions
if( $PWD == $PROJECT_ROOT ) then
    echo "Running sims from working copy root is possible but not "
    echo "recommended. Please run from other directory"
    exit(1)
endif
if( $PWD == $HOME ) then
    echo "Running sims from the user's home directory is possible"
    echo "but not recommended. Please run from other directory"
    exit(1)
endif


# determing main action.
# options are sim and clean
if ( $#argv != 0 ) then
    switch ($argv[1])
        case "clean":
            set mode=clean
            rm -rf INCA_libs
            rm irun.*
            rm ncvlog.log
            rm -rf waves.shm
            exit(0)
            shiftrm
            breaksw

        case "sim":
            set mode=sim
            shift
            breaksw

        default:
            echo "presuming sim"
            set mode=sim
            breaksw
    endsw
endif

# parse and store arguments
while ( $#argv != 0 )
    switch ($argv[1])
        case "--test":
        case "-t":
            set test=$2;
            #echo "test is $test"
            shift
            shift
            breaksw
        case "-d"
        case "--testdir":
            set test_dir=$2;
            #echo "test_dir is $test_dir"
            shift
            shift
            breaksw
        case "-w":
        case "--waves":
            set waves=yes
            shift
            breaksw
        case "-b":
        case "--batch":
            set gui=no
            shift
            breaksw
        case "--seed":
            set randomseed=no
            set userseed=$2
            echo "user random seed is $userseed"
            shift
            shift
            breaksw
        case "--sva":
            set sva=yes
            shift
            breaksw
		case "-c":
		case "--cov":
			set coverage=yes
            shift
            breaksw
        default:
            echo "Invalid arg"
            exit 1
    endsw
end


# simvision command for waveforms.
# 		default saves all signals in design
set WavesScript="$VERIF_ROOT/scripts/waves.tcl"


# Coverage switches
set CoverageCommands=""
#set CoverageCommands="$CoverageCommands "
set CoverageCommands="$CoverageCommands -coverage all" # code and functional coverage. ICC user guide. Also activates cover properties, so no need for -abvcoveron
set CoverageCommands="$CoverageCommands -covfile $VERIF_ROOT/scripts/coverage.tcl"
set CoverageCommands="$CoverageCommands -covdut $dut"		## will not capture coverage from the testbench...

set CoverageCommands="$CoverageCommands -covoverwrite"
set CoverageCommands="$CoverageCommands -covtest $test"


# Main irun switches
# 		VHDL '93 support, -v200x also possible
set MainOptions="$MainOptions -rnm_package" ## real number modeling for SystemVerilog

#set MainOptions="$MainOptions "
set MainOptions="$MainOptions -nowarn COVFHT"
set MainOptions="$MainOptions -nowarn COVCGN"
set MainOptions="$MainOptions -nowarn COVUTA"
set MainOptions="$MainOptions -nowarn ICFCLD"
set MainOptions="$MainOptions -nowarn WSEM2009"

# print out the random seed in the log file to help rerun in case of error
set MainOptions="$MainOptions -input $VERIF_ROOT/scripts/misc_commands.tcl"

# Append optional arguments
if($gui == "yes") then
    set MainOptions="$MainOptions -gui"
	if($waves == "default") then
		set waves="yes"
	endif
endif

if($gui == "no") then
    set MainOptions="$MainOptions -run -exit"
	if($waves == "default") then
		set waves="no"
	endif
endif

if($waves == "yes") then
    set MainOptions="$MainOptions -input $WavesScript -ACCESS +rwc"
endif

if($coverage == "yes") then
	set MainOptions="$MainOptions $CoverageCommands"
endif

## Default: do nothing
if($randomseed == "yes") then
	set MainOptions="$MainOptions -seed random"
else if ($randomseed == "no") then
	set MainOptions="$MainOptions -seed $userseed"
endif

# Build and call irun command
xrun $MainOptions \
     $Models \
     $DesignFiles \
     $TestbenchFiles \
     $assertionfiles
