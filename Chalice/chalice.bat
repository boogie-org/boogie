@echo off

set JAVA_EXE=java

REM Attention: 'where' might not be available on all Windows versions
call where %JAVA_EXE% > NUL
if not %ERRORLEVEL%==0 (
	echo Java could not be started.
	goto :exit_with_error
)

REM Get the Scala version, or rather, a string such as "scala-2.8.1"
for /f "delims=" %%a in ('dir /b project\boot\scala-*') do @set SCALA_DIR=%%a

set CP=
set CP=%CP%;project\boot\%SCALA_DIR%\lib\scala-library.jar
set CP=%CP%;target\%SCALA_DIR%.final\classes

set CHALICE_MAIN=chalice.Chalice

set CHALICE_OPTS=
set CHALICE_OPTS=%CHALICE_OPTS% /boogieOpt:nologo
set CHALICE_OPTS=%CHALICE_OPTS% %*

set CMD=%JAVA_EXE% -cp %CP% %CHALICE_MAIN% %CHALICE_OPTS%

REM echo.
REM echo %CMD%
REM echo.

call %CMD%

exit /B 0


:exit_with_error
exit /B 1