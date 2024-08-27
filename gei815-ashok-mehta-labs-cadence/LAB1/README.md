first lab.

Follow pdf original instructions (GEI815 web site). To select which option (implication, no implication, etc),
change the commented line near the top of the run_script, for example using
gedit run_script.tcsh
or
nano run_script.tcsh



To launch simulation:

at root directory:

tcsh
source sourceme.tcsh
cd LAB1
./run_script.tcsh --sva


In batch mode, run with
./run_script.tcsh --sva --batch 

To have waveforms in batch mode:
./run_script.tcsh --sva --batch --waves
or
./run_script.tcsh --sva -b -w


