@echo off

set differ="C:\Program Files\TortoiseSVN\bin\TortoiseMerge.exe"
if exist %differ% goto :diff
if not exist %differ% goto :txtdiff

:txtdiff
echo ====================================
echo Reference output: %1
echo ------------------------------------
type "%1"
echo ====================================
echo Currenct output: %2
echo ------------------------------------
type "%2"
echo ====================================
goto :eof

:diff
%differ% "%1" "%2"
goto :eof
