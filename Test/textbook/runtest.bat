@echo off

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

REM ======================
REM ====================== Examples written in Boogie
REM ======================
for %%f in (Find.bpl DutchFlag.bpl Bubble.bpl DivMod.bpl McCarthy-91.bpl
            TuringFactorial.bpl) do (
  echo.
  echo ------------------------------ %%f ---------------------
  %BPLEXE% %* %%f
)
