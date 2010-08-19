#!/usr/bin/bash

TESTS="
  LoopSqRoot.chalice
  RecSqRoot.chalice
  SpecStmt.chalice
  SumCubes.chalice
  TestTransform.chalice
  TestRefines.chalice
"
if [ -f Output ]
then
  rm -f Output
fi

for f in $TESTS 
do
  echo "Processing $f" | tee -a Output
  scala -cp ../bin chalice.Chalice -nologo $f >> Output 2>&1
done

if diff Output Answer
then
  echo Success
else
  echo Failure
fi

  
