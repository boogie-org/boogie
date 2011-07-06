@echo off

call scala -cp "%~dp0\bin" chalice.Chalice -nologo %1 %2 %3 %4

exit /B 0
