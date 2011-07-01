@echo off

set chalice="%~dp0\..\..\chalice.bat"

set output="%1.output.txt"

echo Verification of %1.chalice > %output%
echo.>> %output%
call %chalice% "%1.chalice" %2 %3 %4 %5 >> %output% 2>&1

set o=%~dp1%out.bpl
if exist "%o%" copy "%o%" "%1.bpl">nul
if exist "%o%" del "%~dp1%out.bpl"
