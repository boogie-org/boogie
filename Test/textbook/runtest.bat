@echo off

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

REM ======================
REM ====================== Examples written in Boogie
REM ======================
for %%f in (Find.bpl DutchFlag.bpl Bubble.bpl) do (
  echo.
  echo ------------------------------ %%f ---------------------
  %BPLEXE% %* %%f
)
