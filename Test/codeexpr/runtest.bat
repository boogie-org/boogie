@echo off

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (CodeExpr0.bpl CodeExpr1.bpl CodeExpr2.bpl) do (
  echo.
  echo ------------------------------ %%f ---------------------
  %BPLEXE% %* %%f
)
