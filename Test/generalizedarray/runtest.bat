@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (Maps.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BPLEXE% %* /typeEncoding:m /useArrayTheory %%f
)

