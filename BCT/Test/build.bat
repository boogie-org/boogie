@echo off
setlocal

set BCTDIR=..\..\Binaries
set BEXE=%BCTDIR%\BytecodeTranslator.exe
set TESTDIR=Binaries
set TESTEXE=%TESTDIR%\BCTStmtTest.exe

for %%f in (%TESTEXE%) do (
  echo -------------------- %%f --------------------
  call Devenv.exe MySolution.sln /build Release

)

@echo off
rem Usage: runtest.bat <dir>
if "%1" == "" goto noDirSpecified
if not exist %1\nul goto noDirExists
echo ----- Running regression test %1
pushd %1
if not exist runtest.bat goto noRunTest
call Devenv.exe %1.sln /build Debug 

:passTest
echo Succeeded
goto end

:noDirSpecified
echo runtest: Error: Syntax: runtest testDirectory [ additionalTestArguments ... ]
goto errorEnd

:noDirExists
echo runtest: Error: There is no test directory %1
goto errorEnd

:noRunTest
echo runtest: Error: no runtest.bat found in test directory %1
goto errorEnd

:errorEnd
popd
exit /b 1

:end
popd
exit /b 0
