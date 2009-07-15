@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (smoke0.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% /smoke %* %%f
)

