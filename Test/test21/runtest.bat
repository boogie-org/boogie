@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

for %%m in (
              n p a
            ) do (
echo --------------------- TypeEncoding %%m ----------------------------
for %%f in (DisjointDomains.bpl DisjointDomains2.bpl FunAxioms.bpl
            FunAxioms2.bpl PolyList.bpl Maps0.bpl Maps1.bpl
            InterestingExamples0.bpl InterestingExamples1.bpl InterestingExamples2.bpl
            InterestingExamples3.bpl InterestingExamples4.bpl InterestingExamples5.bpl
            Colors.bpl HeapAbstraction.bpl HeapAxiom.bpl Triggers0.bpl Triggers1.bpl
            Keywords.bpl Casts.bpl EmptyList.bpl Boxing.bpl MapOutputTypeParams.bpl
            ParallelAssignment.bpl BooleanQuantification.bpl BooleanQuantification2.bpl
            Flattening.bpl Orderings.bpl Orderings2.bpl Orderings3.bpl Orderings4.bpl
            EmptySetBug.bpl Coercions2.bpl MapAxiomsConsistency.bpl LargeLiterals0.bpl) do (
  echo --------------------- File %%f ----------------------------
  %BGEXE% %* /typeEncoding:%%m /logPrefix:0%%m /bv:n %%f
)

echo --------------------- File NameClash.bpl ----------------------------
%BGEXE% %* /typeEncoding:%%m /logPrefix:0%%m /logPrefix:S NameClash.bpl
echo --------------------- File LetSorting.bpl ----------------------------
%BGEXE% %* /typeEncoding:%%m /logPrefix:0%%m /logPrefix:S /vc:n LetSorting.bpl
echo --------------------- File Keywords.bpl ----------------------------
%BGEXE% %* /typeEncoding:%%m /logPrefix:0%%m /logPrefix:S Keywords.bpl
echo --------------------- File LargeLiterals0.bpl ----------------------------
%BGEXE% %* /typeEncoding:%%m /logPrefix:0%%m /logPrefix:S LargeLiterals0.bpl
)

for %%m in (
              n p a
            ) do (
echo --------------------- TypeEncoding %%m z3types ----------------------------
for %%f in (DisjointDomains.bpl DisjointDomains2.bpl FunAxioms.bpl
            FunAxioms2.bpl PolyList.bpl Maps0.bpl Maps1.bpl
            InterestingExamples0.bpl InterestingExamples1.bpl InterestingExamples2.bpl
            InterestingExamples3.bpl InterestingExamples4.bpl InterestingExamples5.bpl
            Colors.bpl HeapAbstraction.bpl HeapAxiom.bpl Triggers0.bpl Triggers1.bpl
            Keywords.bpl Casts.bpl BooleanQuantification.bpl EmptyList.bpl Boxing.bpl
            MapOutputTypeParams.bpl ParallelAssignment.bpl BooleanQuantification2.bpl
            Flattening.bpl Orderings.bpl Orderings2.bpl Orderings3.bpl Orderings4.bpl
            EmptySetBug.bpl Coercions2.bpl MapAxiomsConsistency.bpl LargeLiterals0.bpl) do (
  echo --------------------- File %%f ----------------------------
  %BGEXE% %* /typeEncoding:%%m /logPrefix:1%%m %%f
)

echo --------------------- File LetSorting.bpl ----------------------------
%BGEXE% %* /typeEncoding:%%m /logPrefix:1%%m /logPrefix:z3t /z3types /vc:n LetSorting.bpl
)
