@echo off

set chalice="%~dp0\..\..\chalice.bat"
set diff="%~dp0\diff.bat"

if not exist "%1.chalice" goto errorNotFound
if not exist "%1.output.txt" goto errorNoRef

set output=output.txt
echo Verification of %1.chalice > %output%
echo.>> %output%
call %chalice% "%1.chalice" %2 %3 %4 %5 %6 %7 >> %output% 2>&1

fc "%1.output.txt" output.txt > nul
if not errorlevel 1 goto passTest
goto failTest

:passTest
echo OK: %1.chalice
goto end

:failTest
echo FAIL: %1.chalice
call %diff% "%1.output.txt" output.txt
goto errorEnd

:errorEnd
if exist out.bpl del out.bpl
if exist output.txt del output.txt
exit /b 1

:end
if exist out.bpl del out.bpl
if exist output.txt del output.txt
exit /b 0

:errorNotFound
echo ERROR: %1.chalice not found.
goto errorEnd

:errorNoRef
echo ERROR: %1.output.txt (reference output) not found.
goto errorEnd
