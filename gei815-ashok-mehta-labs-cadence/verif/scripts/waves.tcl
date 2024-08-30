########################################################################
## Author  :    Marc-Andre Tetrault
## Project :    Verification Primer
##
## Universite de Sherbrooke
########################################################################

# save all waveforms by default. Consult the Simvision user guide
# for details on the commands and how to change recording rules
# if disk space is an issue.

database -open waves -into waves.shm -default

probe -create $::env(LAB_TEST_DUT_NAME) -all -depth all -database waves
