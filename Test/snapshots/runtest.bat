@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (Snapshots0 Snapshots1 Snapshots2 Snapshots3) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /verifySnapshots %%f.bpl
)
