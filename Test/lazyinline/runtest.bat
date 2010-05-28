@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

echo ----- Running regression test bar1.bpl
%BGEXE% %* /noinfer /lazyInline:1 bar1.bpl
echo -----
echo ----- Running regression test bar2.bpl
%BGEXE% %* /noinfer /lazyInline:1 bar2.bpl
echo -----
echo ----- Running regression test bar3.bpl
%BGEXE% %* /noinfer /lazyInline:1 bar3.bpl
echo -----
echo ----- Running regression test bar4.bpl
%BGEXE% %* /noinfer /lazyInline:1 bar4.bpl
echo -----
echo ----- Running regression test bar6.bpl
%BGEXE% %* /noinfer /lazyInline:1 bar6.bpl
echo -----

