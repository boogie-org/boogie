@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (t1.bpl t2.bpl ex.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BPLEXE% %* /typeEncoding:m %%f
)

