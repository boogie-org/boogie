@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

%BGEXE% %* /verifySnapshots Snapshots0.bpl
