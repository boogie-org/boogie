@echo off

REM Regression tests for the refinement extension to Chalice
REM Author: Kuat Yessenov

setlocal EnableDelayedExpansion

set chalice="%~dp0\..\..\chalice.bat"
set output=Output
set answer=Answer
set parameters="-noTermination"
set tests=LoopSqRoot,RecSqRoot,SpecStmt,SumCubes,TestTransform,TestRefines,RecFiniteDiff,LoopFiniteDiff,Pick,TestCoupling,Calculator,AngelicExec,RefinesLoop

REM Remove stale output file
if exist %output% del %output%

echo -------------------------------------
echo Refinement extension regression tests
echo -------------------------------------

REM Process each test
for %%f in (%tests%) do (
  echo Processing %%f.chalice >> %output%
  echo Processing %%f
  
  if exist out.bpl del out.bpl
  call %chalice% "%%f.chalice" "%parameters%" >> %output% 2>&1
)

echo -------------------------------------

REM Compare with the reference

fc %answer% %output% > nul
if not errorlevel 1 goto passTest
goto failTest

:passTest
echo Passed
if exist %output% del %output%
if exist out.bpl del out.bpl
exit /b 0

:failTest
echo Failed (see Output)
exit /b 1

