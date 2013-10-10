@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

echo ----- Running regression test bar1.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i bar1.bpl
echo -----
echo ----- Running regression test bar2.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i bar2.bpl
echo -----
echo ----- Running regression test bar3.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i bar3.bpl
echo -----
echo ----- Running regression test bar4.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i bar4.bpl
echo -----
echo ----- Running regression test bar6.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i bar6.bpl
echo -----
echo ----- Running regression test bar7.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i /nonUniformUnfolding bar7.bpl
echo -----
echo ----- Running regression test bar8.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i /nonUniformUnfolding bar8.bpl
echo -----
echo ----- Running regression test bar9.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i /nonUniformUnfolding bar9.bpl
echo -----
echo ----- Running regression test bar10.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i /nonUniformUnfolding bar10.bpl
echo -----
echo ----- Running regression test bar11.bpl
%BGEXE% %* /stratifiedInline:1 /vc:i bar11.bpl
echo -----

