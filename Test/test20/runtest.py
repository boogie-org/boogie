#!/usr/bin/python

# 2013 Pantazis Deligiannis
#
# runs the test cases of this directory

import sys;
import os;
import getopt;

MONO = "/usr/bin/mono "
BOOGIE = "/Users/pantazis/workspace/boogie/Binaries/Boogie.exe "

PROVER_OPTIONS_Z3 = "/nologo "
PROVER_OPTIONS_CVC4 = "/proverOpt:SOLVER=cvc4 /nologo "

# choose a parser
opts, args = getopt.getopt(sys.argv[1:], "s:", ["solver="])
solver = "Z3"
for o, a in opts:
  if o in ("-s", "--solver"):
      if a == "cvc4":
          solver = a

# if the Output file exists remove it
if os.path.exists("Output"):
  os.remove("Output")

# runs the given test
def runtest(filename):
  if solver == "cvc4":
    if os.name == "nt":
      command = BOOGIE + PROVER_OPTIONS_CVC4 + filename
    else:
	  command = MONO + BOOGIE + PROVER_OPTIONS_CVC4 + filename
  else:
    if os.name == "nt":
      command = BOOGIE + PROVER_OPTIONS_Z3 + filename
    else:
	  command = MONO + BOOGIE + PROVER_OPTIONS_Z3 + filename
  
  print "===== Testing: " + filename
  
  if os.path.exists("Output"):
    os.system(command + " >> Output")
  else:
    os.system(command + " > Output")
    
runtest("TypeDecls0.bpl")
runtest("TypeDecls1.bpl")
runtest("Prog0.bpl")
runtest("Prog1.bpl")
runtest("Prog2.bpl")
runtest("PolyFuns0.bpl")
runtest("PolyFuns1.bpl")
runtest("PolyProcs0.bpl")
runtest("TypeSynonyms0.bpl")
runtest("TypeSynonyms1.bpl")
runtest("TypeSynonyms2.bpl")
runtest("/print:- /env:0 TypeSynonyms0.bpl")
runtest("/print:- /env:0 /printDesugared TypeSynonyms2.bpl")
runtest("PolyPolyPoly.bpl")
runtest("PolyPolyPoly2.bpl")
runtest("ProcParamReordering.bpl")
runtest("ParallelAssignment.bpl")
runtest("ParallelAssignment2.bpl")
runtest("Coercions.bpl")
runtest("EmptySeq.bpl")

# compare the output with the expected answers
test_file = open("Output").readlines()
correct_file = open("Answer").readlines()

for test, correct in zip(test_file, correct_file):
    if test.strip(' \t\n\r') != correct.strip(' \t\n\r'):
        print "\n===== " + os.getcwd().split(os.sep)[-1] + ": FAILED"
        break
else:
    print "\n===== " + os.getcwd().split(os.sep)[-1] + ": PASSED"
