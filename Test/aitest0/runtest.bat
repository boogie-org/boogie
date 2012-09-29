@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

%BGEXE% %* -infer:j -instrumentInfer:e -printInstrumented -noVerify constants.bpl
%BGEXE% %* -infer:j Intervals.bpl
