########################################################################
## Author  :    Marc-Andre Tetrault
## Project :    Verification Primer
##
## Universite de Sherbrooke
########################################################################
# manifest file for testbench components
########################################################################

$VERIF_ROOT/core/tb_constrainedrandom.sv
$VERIF_ROOT/core/tb_flowcontrol.sv

$VERIF_ROOT/core/tb_waveformgen.sv
$VERIF_ROOT/core/tb_clockgen.sv
$VERIF_ROOT/core/tb_top.sv

#  Move to assertions manifest file, for easier switch in srun
# $VERIF_ROOT/assertions/ChannelCheckers.sv
