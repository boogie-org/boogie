@echo off

set regtest="%~dp0\reg_test.bat"

for /F %%f in ('dir *.chalice /b') do (
  call %regtest% %%~nf %1 %2 %3 %4 %5 %6 %7 %8
)

exit /b 0
