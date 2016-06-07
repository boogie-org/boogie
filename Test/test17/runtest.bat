@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe


for %%f in (contractinfer flpydisk) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /errorLimit:1 /contractInfer /z3mam:4 /subsumption:0 %%f.bpl
)
