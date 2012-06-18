@echo off
rem Usage: runtest.bat <dir> [runtimeChecking]
if "%1" == "" goto noDirSpecified
if "%1" == "runtimeChecking" goto noDirSpecified
if not exist %1\nul goto noDirExists
pushd %1
if "%2" == "runtimeChecking" goto RuntimeChecking
:NoRuntimeChecking
echo ----- Running regression test %1 (without runtime checking)
if not exist runtestNoRuntimeChecking.bat goto noRunTestNoRuntimeChecking
call runtestNoRuntimeChecking.bat -nologo -logPrefix:%1 > OutputNoRuntimeChecking
rem There seem to be some race between finishing writing to the Output file, and running fc.
rem Calling fc twice seems to fix (or at least alleviate) the problem.
fc /W AnswerNoRuntimeChecking OutputNoRuntimeChecking > nul
fc /W AnswerNoRuntimeChecking OutputNoRuntimeChecking > nul
goto Continue
:RuntimeChecking
echo ----- Running regression test %1 (with runtime checking)
if not exist runtestRuntimeChecking.bat goto noRunTestRuntimeChecking
call runtestRuntimeChecking.bat -nologo -logPrefix:%1 > OutputRuntimeChecking
rem There seem to be some race between finishing writing to the Output file, and running fc.
rem Calling fc twice seems to fix (or at least alleviate) the problem.
fc /W AnswerRuntimeChecking OutputRuntimeChecking > nul
fc /W AnswerRuntimeChecking OutputRuntimeChecking > nul
:Continue
if not errorlevel 1 goto passTest
echo %1 FAILED
goto errorEnd

:passTest
echo %1 Succeeded
goto end

:noDirSpecified
echo runtest: Error: Syntax: runtest testDirectory [ additionalTestArguments ... ]
goto errorEnd

:noDirExists
echo runtest: Error: There is no test directory %1
goto errorEnd

:noRunTestNoRuntimeChecking
echo runtest: Error: no runtestNoRuntimeChecking.bat found in test directory %1
goto errorEnd

:noRunTestRuntimeChecking
echo runtest: Error: no runtestRuntimeChecking.bat found in test directory %1
goto errorEnd

:errorEnd
popd
exit /b 1

:end
popd
exit /b 0
