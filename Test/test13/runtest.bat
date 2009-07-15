@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (ErrorTraceTestLoopInvViolationBPL) do (
  echo.
  echo -------------------- %%f --------------------
  "%BPLEXE%" %* %%f.bpl
)
