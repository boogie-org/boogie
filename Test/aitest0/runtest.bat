@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

%BGEXE% %* -infer:c -printInstrumented -noVerify constants.bpl
