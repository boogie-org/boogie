@echo off

call scala -cp "%~dp0\bin" chalice.Chalice -nologo %*

exit /B 0
