
@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

echo -------------------- Snapshots0.bpl --------------------
%BGEXE% %* /verifySnapshots Snapshots0.bpl

echo.
echo -------------------- Snapshots1.bpl --------------------
%BGEXE% %* /verifySnapshots Snapshots1.bpl

echo.
echo -------------------- Snapshots2.bpl --------------------
%BGEXE% %* /verifySnapshots Snapshots2.bpl
