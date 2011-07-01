@echo off

set getboogieoutput="%~dp0\getboogieoutput.bat"

for /F %%f in ('dir *.chalice /b') do (
  echo   Generating reference for %%~nf.chalice ...
  call %getboogieoutput% %%~nf %1 %2 %3 %4 %5 %6 %7
)

exit /b 0
