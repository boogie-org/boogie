@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BPLEXE=%BOOGIEDIR%\Boogie.exe

echo -------------------- LoopUnroll.bpl /loopUnroll:1 --------------------
"%BPLEXE%" %* /loopUnroll:1 /logPrefix:-lu1 LoopUnroll.bpl
echo -------------------- LoopUnroll.bpl /loopUnroll:2 --------------------
"%BPLEXE%" %* LoopUnroll.bpl /logPrefix:-lu2 /proc:ManyIterations /loopUnroll:2
echo -------------------- LoopUnroll.bpl /loopUnroll:3 --------------------
"%BPLEXE%" %* LoopUnroll.bpl /logPrefix:-lu3 /proc:ManyIterations /loopUnroll:3

