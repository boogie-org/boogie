@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (ineq.bpl Linear0.bpl Linear1.bpl Linear2.bpl
     Linear3.bpl Linear4.bpl Linear5.bpl Linear6.bpl
     Linear7.bpl Linear8.bpl Linear9.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% %* -infer:p -instrumentInfer:e -printInstrumented -noVerify %%f
)

for %%f in (Bound.bpl) do (
  echo -------------------- %%f -------------------- 
  %BGEXE% %* -infer:p %%f
)

