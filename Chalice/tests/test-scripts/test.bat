@echo off

set chalice="%~dp0\..\..\chalice.bat"
set getparams="%~dp0\getparams.bat"

if not exist "%1.chalice" goto errorNotFound

:: get parameters
set chaliceparameters=
setlocal EnableDelayedExpansion
set done=0
set key=a
FOR /F "usebackq tokens=1,2 delims==" %%i in (%1.chalice) do (
    
    if !done!==0 (
        set key=%%i
        set param=%%j
    )
    
    set done=1
)
set str=// chalice-parameter
if "!key!"=="!str!" (
    set chaliceparameters=!param!
)

set output=output.txt
echo Verification of %1.chalice using parameters="%chaliceparameters%" > %output%
echo.>> %output%
call %chalice% "%1.chalice" %chaliceparameters% %2 %3 %4 %5 %6 %7 >> %output% 2>&1
type %output%

exit /B 0

:errorNotFound
echo ERROR: %1.chalice not found.
exit /B 1
