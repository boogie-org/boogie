@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (doomed.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% /vc:doomed %* %%f
)

for %%f in (notdoomed.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% /vc:doomed %* %%f
)

