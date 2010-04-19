@echo off
setlocal

set BCTDIR=..\..\Binaries
set BEXE=%BCTDIR%\BytecodeTranslator.exe

if not exist Output.txt goto justRunTest
del Output.txt

:justRunTest
for %%f in (*.cs) do (
  echo -------------------- %%f --------------------
  csc /nologo /t:library /debug %%~nf.cs
  %BEXE% %%~nf.dll
  type %%~nf.bpl >> Output.txt
)



