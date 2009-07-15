@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (VarMapFixPoint.bpl TestIntervals.bpl) do (
  echo. 
  echo -------------------- %%f -------------------- 
  %BPLEXE% %* %%f /infer:i
)
