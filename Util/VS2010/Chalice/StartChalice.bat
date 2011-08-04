@echo off
echo ---------- Starting ------------ < nul >> c:\tmp\coo.out
time < nul >> c:\tmp\coo.out
echo. < nul >> c:\tmp\coo.out

call "c:\Program Files\Scala\bin\scala" -cp c:\boogie\Chalice\target\scala-2.8.1.final\classes chalice.Chalice /boogieOpt:nologo /vs %* 2>> c:\tmp\coo.out

time < nul >> c:\tmp\coo.out
echo. < nul >> c:\tmp\coo.out
echo ---------- Done ------------ < nul >> c:\tmp\coo.out
