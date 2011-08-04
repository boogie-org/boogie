@echo off

call scala -cp "%~dp0\target\scala-2.8.1.final\classes" chalice.Chalice /boogieOpt:nologo %*

exit /B 0
