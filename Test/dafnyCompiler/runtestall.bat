@echo off
setlocal

set errors=0

for /F "eol=; tokens=1,2,3*" %%i in (compilerTests.txt) do if %%j==Use call runtest.bat %%i %1 %2 %3 %4 %5 %6 %7 %8 %9 || set errors=1

for /F "eol=; tokens=1,2,3*" %%i in (compilerTests.txt) do if %%j==Use call runtest.bat %%i %1 %2 %3 %4 %5 %6 %7 %8 %9 runtimeChecking || set errors=1

exit /b %errors%
