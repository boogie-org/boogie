@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

%BGEXE% %* /verifySnapshots /verifySeparately Snapshots0.bpl Snapshots1.bpl Snapshots2.bpl Snapshots3.bpl Snapshots4.bpl Snapshots5.bpl

