@echo off
setlocal

set JENNISYS_EXE=..\..\Jennisys\Jennisys\bin\Debug\Jennisys.exe

for %%f in (Prog0.jen ExtensibleArray.jen) do (
  echo.
  echo -------------------- %%f --------------------
  %JENNISYS_EXE% %* /trace %%f
)
