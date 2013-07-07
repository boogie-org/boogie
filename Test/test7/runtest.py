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
  
  if filename == "SeparateVerification0.bpl":
    os.system("echo ----- SeparateVerification0.bpl >> Output")
  elif filename == "SeparateVerification1.bpl SeparateVerification0.bpl":
    os.system("echo ----- SeparateVerification1.bpl SeparateVerification0.bpl >> Output")
  elif filename == "SeparateVerification0.bpl SeparateVerification0.bpl":
    os.system("echo ----- SeparateVerification0.bpl SeparateVerification0.bpl >> Output")
  elif filename == "SeparateVerification0.bpl SeparateVerification0.bpl SeparateVerification1.bpl":
    os.system("echo ----- SeparateVerification0.bpl SeparateVerification0.bpl SeparateVerification1.bpl >> Output")
  
  if os.path.exists("Output"):
    os.system(command + " >> Output")
  else:
    os.system(command + " > Output")

os.system("echo ------------------------------ NestedVC.bpl --------------------- >> Output")
runtest("/vc:nested NestedVC.bpl")

os.system("echo ------------------------------ UnreachableBlocks.bpl --------------------- >> Output")
runtest("/vc:nested UnreachableBlocks.bpl")

os.system("echo ------------------------------ MultipleErrors.bpl --------------------- >> Output")

modes = ["block", "local", "dag"]

for mode in modes:
  os.system("echo >> Output")
  os.system("echo ----- /vc:" + mode + " >> Output")
  runtest("/errorLimit:1 /errorTrace:1 /vc:" + mode + " /logPrefix:-1" + mode + " MultipleErrors.bpl")

modes = ["local", "dag"]

for mode in modes:
  os.system("echo >> Output")
  os.system("echo ----- /errorLimit:10 /vc:" + mode + " >> Output")
  runtest("/errorLimit:10 /errorTrace:1 /vc:" + mode + " /logPrefix:-10" + mode + " MultipleErrors.bpl")

# compare the output with the expected answers
test_file = open("Output").readlines()
correct_file = open("Answer").readlines()

for test, correct in zip(test_file, correct_file):
    if test.strip(' \t\n\r') != correct.strip(' \t\n\r'):
        print "\n===== " + os.getcwd().split(os.sep)[-1] + ": FAILED"
        break
else:
    print "\n===== " + os.getcwd().split(os.sep)[-1] + ": PASSED"
