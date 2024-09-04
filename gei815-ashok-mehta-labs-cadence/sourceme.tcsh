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
setenv VERIF_ROOT                   $PROJECT_ROOT/verif


################################################################
# Load Cadence tools
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

# Licence patch. See instructor if issue with vManager licence.
setenv  HOSTALIASES $PROJECT_ROOT/.hosts_local

# Override multiple licence servers - creates delays
setenv CDS_LIC_FILE 6055@cadence.gegi.usherbrooke.ca:7055@cadence.gegi.usherbrooke.ca
################################################################


################################################################

