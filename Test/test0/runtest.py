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

#runtest("Prog0.bpl")
#runtest("ModifiedBag.bpl")
runtest("Triggers0.bpl")
runtest("Triggers1.bpl")
runtest("/printInstrumented PrettyPrint.bpl")
runtest("Arrays0.bpl")
runtest("Arrays1.bpl")
runtest("Types0.bpl")
runtest("Types1.bpl")
runtest("WhereParsing.bpl")
runtest("WhereParsing0.bpl")
runtest("WhereParsing1.bpl")
runtest("WhereParsing2.bpl")
runtest("WhereResolution.bpl")
runtest("BadLabels0.bpl")
runtest("BadLabels1.bpl")
runtest("LineParse.bpl")
runtest("LineResolve.bpl")
runtest("AttributeParsingErr.bpl")
#runtest("/print:- /env:0 AttributeParsing.bpl")
runtest("AttributeResolution.bpl")
#runtest("/print:- /env:0 Quoting.bpl")
runtest("LargeLiterals0.bpl")
runtest("MapsResolutionErrors.bpl")
runtest("Orderings.bpl")
runtest("BadQuantifier.bpl")
#runtest("EmptyCallArgs.bpl")
runtest("SeparateVerification0.bpl")
runtest("SeparateVerification1.bpl SeparateVerification0.bpl")
runtest("SeparateVerification0.bpl SeparateVerification0.bpl")
#runtest("SeparateVerification0.bpl SeparateVerification0.bpl SeparateVerification1.bpl")

# compare the output with the expected answers
test_file = open("Output").readlines()
correct_file = open("Answer").readlines()

for test, correct in zip(test_file, correct_file):
    if test.strip(' \t\n\r') != correct.strip(' \t\n\r'):
        print "\n===== " + os.getcwd().split(os.sep)[-1] + ": FAILED"
        break
else:
    print "\n===== " + os.getcwd().split(os.sep)[-1] + ": PASSED"
