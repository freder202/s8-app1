#! /bin/tcsh
########################################################################
## Author  :    Marc-André Tétrault
## Project :    Verification Primer
##
## Université de Sherbrooke
################################################################################
#
# Purpose   :   Verification environment setup
#               - Variables
#               - Aliases
#               - Software environment/version selection
################################################################################

# set environment working copy root
setenv PROJECT_ROOT                 $PWD


################################################################
# Load Cadence tools
################################################################
# Xcellium, very recent Cadence simulator package
setenv SIM    xcelium

if( $?CMC_HOME == 0) then
        setenv CMC_HOME /CMC
endif

source $CMC_HOME/scripts/cadence.2014.12.csh

setenv CMC_CDS_XCELIUM_ARCH ${CMC_CDS_ARCH}
setenv CMC_CDS_XCELIUM_HOME ${CDS_TOP_DIR}/XCELIUMMAIN23.09.006_${CMC_CDS_XCELIUM_ARCH}

setenv PATH ${CMC_CDS_XCELIUM_HOME}/bin:${PATH}
setenv PATH ${CMC_CDS_XCELIUM_HOME}/tools.lnx86/bin:${PATH}

##In order to enable coverage analysis, please set the environment variable MDV_XLM_HOME to point to the XCELIUM$
setenv MDV_XLM_HOME $CMC_CDS_XCELIUM_HOME

# Le mode de régression local n'est plus disponible après 23.03.002. Rester à celle-ci pour le moment
source $CMC_HOME/scripts/cadence.vmanager23.03.002.csh
#source $CMC_HOME/scripts/cadence.vmanager23.09.002.csh

# Licence patch. See instructor if issue with vManager licence.
setenv  HOSTALIASES $PROJECT_ROOT/.hosts_local

# Override multiple licence servers - creates delays
setenv CDS_LIC_FILE 6055@cadence.gegi.usherbrooke.ca:7055@cadence.gegi.usherbrooke.ca
################################################################



################################################################
# Create shortcut for Pycharm
################################################################

if ( -f "/opt/pycharm-2024/bin/pycharm.sh" ) then
    # use lab workstation local installation
    alias pycharm /opt/pycharm-2024/bin/pycharm.sh
else
    echo "Installation locale de Pycharm non disponible"
    echo "Utilisez l'éditeur de votre choix."
endif

################################################################
# Verification environment local setup
################################################################


setenv DESIGN_ROOT	                $PROJECT_ROOT/design
setenv VERIF_ROOT	                  $PROJECT_ROOT/verif
setenv DUT_INST_NAME                top
setenv MODELS_HLM_ROOT	            $DESIGN_ROOT/analog/hlm
setenv MODELS_MLM_ROOT	            $DESIGN_ROOT/analog/mlm

setenv VMANAGER_CONFIG_HOME         $VERIF_ROOT/vmanager
setenv VMANAGER_REGRESSIONS_AREA    $VERIF_ROOT/regression_area
setenv PYTHONPATH                   $VERIF_ROOT/tests:$VERIF_ROOT/core:$VERIF_ROOT/core/cocotb_sanitycheck

# Simulation command
alias srun $VERIF_ROOT/scripts/runsim.py

# Vmanager in standalone mode
# with GUI
alias vmanager \vmanager -cs -64 -gui -local $VERIF_ROOT/vmgr_db
#alias vplanner \vplanner -standalone $VERIF_ROOT/vmgr_db

# command line mode, for operation on headless cluster
#alias cmanager \vmanager -cs -64 -batch -local $VERIF_ROOT/vmgr_db

# Vmanager in server mode
#alias smanager \vmanager -cs -64 -gui -server servername.cmc.ca:8080




