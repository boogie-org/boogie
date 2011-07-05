@echo off

set generatereference="%~dp0\generate_reference.bat"

for /F %%f in ('dir *.chalice /b') do (
  call %generatereference% %%~nf %1 %2 %3 %4 %5 %6 %7
)

exit /b 0
