#! /bin/tcsh
########################################################################
## Author  :    Marc-André Tétrault
## Project :    Verification Primer/GEI815
##
## Université de Sherbrooke
################################################################################
#
# Purpose   :   Verification environmen setup
#               - Variables
#               - Aliases
#               - Software environment/version selection
################################################################################


setenv PROJECT_ROOT                 $PWD

setenv DESIGN_ROOT                  $PROJECT_ROOT/design
setenv VERIF_ROOT                   $PROJECT_ROOT/verif
setenv MODELS_HLM_ROOT	            $DESIGN_ROOT/models
setenv MODELS_MLM_ROOT	            $DESIGN_ROOT/models/mlm


################################################################
# Load Cadence tools
source $CMC_HOME/scripts/cadence.incisive15.20.079.csh

# Fix licence timeout from ghost servers
setenv CDS_LIC_FILE 6055@cadence.gegi.usherbrooke.ca

# Fix licence for coverage and regression
setenv  HOSTALIASES $PROJECT_ROOT/.hosts_local
################################################################

alias srun $VERIF_ROOT/scripts/runsim.tcsh
