@echo off
SetLocal EnableDelayedExpansion

set ROOT_DIR=%~dp0
set JAVA_EXE=java 

REM Attention: 'where' might not be available on all Windows versions
call where %JAVA_EXE% > NUL
if not %ERRORLEVEL%==0 (
	echo Java could not be started.
	goto :exit_with_error
)


set SCALA_DIR=scala-2.8.1

REM Set classpath elements
set __CP.SCALA_LIB="%ROOT_DIR%project\boot\%SCALA_DIR%\lib\scala-library.jar"
set __CP.CHALICE="%ROOT_DIR%target\%SCALA_DIR%.final\classes"

REM Assemble classpath and check if all classpath elements exist
set CP=
for /f "tokens=2* delims=.=" %%A in ('set __CP.') do (
	REM echo %%A %%B
	if not exist %%B (
		echo %%B does not exist.
		goto :exit_with_error
	) else (
		set CP=!CP!;%%B
	)
)

REM Chalice main class
set CHALICE_MAIN=chalice.Chalice

REM Chalice command line options
set CHALICE_OPTS=
set CHALICE_OPTS=%CHALICE_OPTS% /boogieOpt:nologo
set CHALICE_OPTS=%CHALICE_OPTS% /boogieOpt:noinfer
set CHALICE_OPTS=%CHALICE_OPTS% /boogie:C:\Users\Alex\Downloads\nightly\Boogie.exe
set CHALICE_OPTS=%CHALICE_OPTS% %*

REM Assemble main command
set CMD=%JAVA_EXE% -cp %CP% -Xss16M %CHALICE_MAIN% %CHALICE_OPTS%

REM echo.
REM echo %CMD%
REM echo.

call %CMD%

exit /B 0


:exit_with_error
exit /B 1
