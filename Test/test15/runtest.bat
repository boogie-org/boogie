@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\boogie.exe

for %%f in (NullInModel IntInModel ModelTest) do (
  echo.
  echo -------------------- %%f --------------------
  "%BGEXE%" %* %%f.bpl /printModel:2
)
for %%f in (InterpretedFunctionTests) do (
  echo.
  echo -------------------- %%f --------------------
  "%BGEXE%" %* %%f.bpl 
)
