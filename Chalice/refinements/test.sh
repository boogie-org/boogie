#!/usr/bin/bash

# Regression tests for refinement extension
# Author: Kuat Yessenov

TESTS="
  LoopSqRoot.chalice
  RecSqRoot.chalice
  SpecStmt.chalice
  SumCubes.chalice
  TestTransform.chalice
  TestRefines.chalice
  RecFiniteDiff.chalice
  LoopFiniteDiff.chalice
  Pick.chalice
  TestCoupling.chalice
  Calculator.chalice
  AngelicExec.chalice
"

# Switch to test directory
CURRENT=`pwd`
cd `dirname $0`

# Remove stale output file
if [ -f Output ]
then
  rm -f Output
fi

# Process tests
START=`date +%s`
for f in ${TESTS}
do
  echo "Processing $f" | tee -a Output
  scala -cp ../bin chalice.Chalice -nologo -noTermination $f >> Output 2>&1
done
END=`date +%s`
echo "Time: $(( $END - $START )) seconds"

# Compare with answer
if diff Output Answer
then
  rm Output
  rm out.bpl
  echo Success
else
  echo Failure
fi

# Switch back to current directory
cd ${CURRENT}
