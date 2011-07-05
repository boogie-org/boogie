@echo off
set getboogieoutput="%~dp0\getboogieoutput.bat"

echo   Generating reference for %1.chalice ...
call %getboogieoutput% %1 %2 %3 %4 %5 %6 %7

exit /b 0
