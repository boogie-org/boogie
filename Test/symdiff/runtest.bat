@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

%BGEXE% %* /z3multipleErrors /errorTrace:0 foo.bpl


