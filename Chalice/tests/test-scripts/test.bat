@echo off

set chalice="%~dp0\..\..\chalice.bat"
set getparams="%~dp0\getparams.bat"

if not exist "%1.chalice" goto errorNotFound

set output=output.txt
set chaliceparameters=
call %getparams% %1 chaliceparameters
echo Verification of %1.chalice using parameters="%chaliceparameters%" > %output%
echo.>> %output%
call %chalice% "%1.chalice" %chaliceparameters% %2 %3 %4 %5 %6 %7 >> %output% 2>&1
type %output%

exit /B 0

:errorNotFound
echo ERROR: %1.chalice not found.
exit /B 1
