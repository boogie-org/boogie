@echo off

setlocal EnableDelayedExpansion

:: no-summary command line parameter
set nosummary=0
if "%1"=="-no-summary" (
    set nosummary=1
    SHIFT
)

set t=0
set c=0
for %%f in (examples permission-model general-tests regressions predicates) do (
  echo Running tests in %%f ...
  echo ------------------------------------------------------
  cd %%f
  set tt=0
  for %%f in (*.chalice) do set /A tt+=1
  call reg_test_all.bat -no-summary %1 %2 %3 %4 %5
  set /A c=!c!+!errorlevel!
  set /A t=!t!+!tt!
  cd ..
  echo ------------------------------------------------------
)

REM Run refinement regression tests
cd refinements
call test.bat
cd ..

if !nosummary!==0 (
    echo.
    if !c!==0 (echo SUMMARY: completed !t! tests successfully.) else (echo SUMMARY: !c! of !t! tests failed.)
)

exit /b !c!
