@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

echo ----- Running regression test bar1.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 bar1.bpl
echo -----
echo ----- Running regression test bar2.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 bar2.bpl
echo -----
echo ----- Running regression test bar3.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 bar3.bpl
echo -----
echo ----- Running regression test bar4.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 bar4.bpl
echo -----
echo ----- Running regression test bar6.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 bar6.bpl
echo -----
echo ----- Running regression test bar7.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 /nonUniformUnfolding bar7.bpl
echo -----
echo ----- Running regression test bar8.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 /nonUniformUnfolding bar8.bpl
echo -----
echo ----- Running regression test bar9.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 /nonUniformUnfolding bar9.bpl
echo -----
echo ----- Running regression test bar10.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 /nonUniformUnfolding bar10.bpl
echo -----
echo ----- Running regression test bar11.bpl
%BGEXE% %* /noinfer /stratifiedInline:1 bar11.bpl
echo -----

