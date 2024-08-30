#! /bin/tcsh
########################################################################
## Author  :    Marc-Andre Tetrault
## Project :    Verification Primer
##
## Universite de Sherbrooke
########################################################################
#
# Purpose   :   Script wrapper for vManager
#
########################################################################

# set defaults
set batch=""
set waves=""

if (! $?BRUN_TEST_NAME) then
  echo "BRUN variables are undefined"
  exit 1
endif


## determine run mode
switch ($BRUN_RUN_MODE)
    case "interactive":
        set batch=""
        set waves=""
        breaksw
    case "interactive_debug":
        set batch=""
        set waves="-w"
        breaksw
    case "batch":
        set batch="-b"
        set waves=""
        breaksw
    case "batch_debug" :
        set batch="-b"
        set waves="-w"
        breaksw
    default:
        echo "unsupported vmanager run mode"
        exit 1
        breaksw
endsw

echo $VERIF_ROOT/scripts/runsim.py $batch $waves --sva --cov --test $BRUN_TEST_NAME --seed $BRUN_SV_SEED
$VERIF_ROOT/scripts/runsim.py $batch $waves --sva --cov --test $BRUN_TEST_NAME --seed $BRUN_SV_SEED
