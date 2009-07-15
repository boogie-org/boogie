@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (houd1.bpl houd2.bpl houd3.bpl houd4.bpl houd5.bpl houd6.bpl houd7.bpl houd8.bpl houd9.bpl houd10.bpl houd11.bpl houd12.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /prover:z3 /Houdini:ci %%f
rem  %BGEXE% %* /nologo /prover:z3api /Houdini:ci %%f
)
