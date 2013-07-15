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
    
modes = ["n", "p", "a"]

files = ["DisjointDomains.bpl", "DisjointDomains2.bpl", "FunAxioms.bpl",
  "FunAxioms2.bpl", "PolyList.bpl", "Maps0.bpl", "Maps1.bpl",
  "InterestingExamples0.bpl", "InterestingExamples1.bpl", "InterestingExamples2.bpl",
  "InterestingExamples3.bpl", "InterestingExamples4.bpl", "InterestingExamples5.bpl",
  "Colors.bpl", "HeapAbstraction.bpl", "HeapAxiom.bpl", "Triggers0.bpl", "Triggers1.bpl",
  "Keywords.bpl", "Casts.bpl", "BooleanQuantification.bpl", "EmptyList.bpl", "Boxing.bpl",
  "MapOutputTypeParams.bpl", "ParallelAssignment.bpl", "BooleanQuantification2.bpl",
  "Flattening.bpl", "Orderings.bpl", "Orderings2.bpl", "Orderings3.bpl", "Orderings4.bpl",
  "EmptySetBug.bpl", "Coercions2.bpl", "MapAxiomsConsistency.bpl", "LargeLiterals0.bpl",
  "Real.bpl"]

for mode in modes:
  os.system("echo >> Output")
  os.system("echo --------------------- TypeEncoding " + mode + " z3types ---------------------------- >> Output")
  for file in files:
    os.system("echo --------------------- File " + file + " ---------------------------- >> Output")
    runtest("/typeEncoding:" + mode + " /logPrefix:0" + mode + " " + file)

  os.system("echo --------------------- File NameClash.bpl ---------------------------- >> Output")
  runtest("/typeEncoding:" + mode + " /logPrefix:0" + mode + " NameClash.bpl")

  os.system("echo --------------------- File Keywords.bpl ---------------------------- >> Output")
  runtest("/typeEncoding:" + mode + " /logPrefix:0" + mode + " Keywords.bpl")

  os.system("echo --------------------- File LargeLiterals0.bpl ---------------------------- >> Output")
  runtest("/typeEncoding:" + mode + " /logPrefix:0" + mode + " LargeLiterals0.bpl")

  os.system("echo --------------------- File LetSorting.bpl ---------------------------- >> Output")
  runtest("/typeEncoding:" + mode + " /logPrefix:0" + mode + " LetSorting.bpl")

# compare the output with the expected answers
test_file = open("Output").readlines()
correct_file = open("Answer").readlines()

for test, correct in zip(test_file, correct_file):
    if test.strip(' \t\n\r') != correct.strip(' \t\n\r'):
        print "\n===== " + os.getcwd().split(os.sep)[-1] + ": FAILED"
        break
else:
    print "\n===== " + os.getcwd().split(os.sep)[-1] + ": PASSED"
