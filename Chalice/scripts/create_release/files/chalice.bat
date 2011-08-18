@echo off

call scala -cp chalice.jar chalice.Chalice /boogieOpt:nologo %*

exit /B 0
