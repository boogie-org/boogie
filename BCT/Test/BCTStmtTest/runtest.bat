@echo off
setlocal

set BCTDIR=..\..\Binaries
set BEXE=%BCTDIR%\BytecodeTranslator.exe
set TESTDIR=Binaries
set TESTEXE=%TESTDIR%\BCTStmtTest.exe

for %%f in (%TESTEXE%) do (
  echo -------------------- %%f --------------------
  %BEXE% %* %%f
)

