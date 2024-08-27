########################################################################
## Author  :    Marc-Andre Tetrault
## Project :    Verification Primer
##
## Universite de Sherbrooke
########################################################################
#
# Purpose   :   Misc Commands sent to simulator
########################################################################


# get the seed. Reference: "SystemVerilog Reference" from Cadence Help tool (cdnshelp)
set RetrievedSeed [set svseed]
puts "The SystemVerilog seed is $RetrievedSeed"

# set severity_pack_assert_off {warning}
# set pack_assert_off {  numeric_std }
