@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe

%BGEXE% %* ..\textbook\bubble.bpl
%DAFNY_EXE% /compile:0 %* ..\dafny1\Celebrity.dfy