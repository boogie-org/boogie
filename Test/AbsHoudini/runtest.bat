@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (f1.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer /abstractHoudini:PredicateAbs %%f
)

