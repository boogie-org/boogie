@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

%BGEXE% %* Lock.bpl
%BGEXE% %* LockIncorrect.bpl
