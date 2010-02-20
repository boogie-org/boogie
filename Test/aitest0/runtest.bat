@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

%BGEXE% %* -infer:c -instrumentInfer:e -printInstrumented -noVerify constants.bpl
