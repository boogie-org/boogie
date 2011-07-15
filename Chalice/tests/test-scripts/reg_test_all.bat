@echo off

setlocal EnableDelayedExpansion

:: no-summary command line parameter
set nosummary=0
if "%1"=="-no-summary" (
    set nosummary=1
    SHIFT /1
)

set regtest="%~dp0\reg_test.bat"
set t=0
set c=0
for /F %%f in ('dir *.chalice /b') do (
  call %regtest% -no-diff %%~nf %1 %2 %3 %4 %5 %6 %7 %8
  set /A c=!c!+!errorlevel!
  set /A t=!t!+1
)
if !nosummary!==0 (
    echo.
    if !c!==0 (echo SUMMARY: completed !t! tests successfully.) else (echo SUMMARY: failed !c! of !t! tests.)
)
exit /b !c!
