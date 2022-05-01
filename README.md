PHIL-4140 INTERMEDIATE LOGIC Project : Convertor proof from Natural Deduction to Sequent System

Authors: Yuanyi Zhang

Description:

This program is write in Python and it will convert valid proofs in Aris as BRAM file (https://aris.bram-hub.com/#) for 
Natural Deduction to valid proofs in Slate as SLT file for Sequent System. The main file will be PHIL_project.py, which is the 
file to run with. When run the program in Python environment, simply type the filename of the input BRAM file and the output file 
will be the filename with '_output' at end as SLT file. If something is wrong, there will be error notification. 

Notes:

There are several restrictions on the input BRAM file. 

1. Contradiction should not be in any premise, SLT files cannot have contradiction symbols. 
2. The input BRAM file proof should be directly save from Aris, and the Aris version should be the same 
as of 4/21/2022. 
3. The input BRAM file proof from Aris should be valid. 
4. The input BRAM file proof from Aris should have only one conclusion.
5. The input BRAM file proof from Aris should not have useless steps, which means that except for the conclusion, 
every other step should have steps followed by them.

Code Requirements:

Python 3.9
