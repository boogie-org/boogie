@echo off
echo ---------- Starting ------------ < nul >> c:\tmp\coo.out
time < nul >> c:\tmp\coo.out
echo. < nul >> c:\tmp\coo.out

call "c:\Program Files\Scala\bin\scala" -cp c:\boogie\Chalice\bin Chalice -nologo -vs -noDeadlockChecks %* 2>> c:\tmp\coo.out

time < nul >> c:\tmp\coo.out
echo. < nul >> c:\tmp\coo.out
echo ---------- Done ------------ < nul >> c:\tmp\coo.out
