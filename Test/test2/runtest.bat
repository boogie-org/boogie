@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

for %%f in (FormulaTerm.bpl FormulaTerm2.bpl Passification.bpl B.bpl
            Ensures.bpl Old.bpl OldIllegal.bpl Arrays.bpl Axioms.bpl
            Quantifiers.bpl Call.bpl AssumeEnsures.bpl
            CutBackEdge.bpl False.bpl LoopInvAssume.bpl
            strings-no-where.bpl strings-where.bpl
            Structured.bpl Where.bpl UpdateExpr.bpl
            NeverPattern.bpl NullaryMaps.bpl Implies.bpl
            IfThenElse1.bpl Lambda.bpl LambdaPoly.bpl LambdaOldExpressions.bpl
            SelectiveChecking.bpl FreeCall.bpl AssumptionVariables0.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /noinfer %%f
)

for %%f in (Arrays.bpl Lambda.bpl TypeEncodingM.bpl ) do (
  echo.
  echo -------------------- %%f /typeEncoding:m --------------------
  %BGEXE% %* /noinfer /typeEncoding:m %%f
)

echo -------------------- sk_hack.bpl --------------------
%BGEXE% %* /noinfer sk_hack.bpl

for %%f in (ContractEvaluationOrder.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* %%f
)

echo.
echo -------------------- Timeouts0.bpl --------------------
%BGEXE% %* /timeLimit:4 Timeouts0.bpl
