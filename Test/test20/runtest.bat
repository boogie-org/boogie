@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

%BGEXE% %* /noVerify TypeDecls0.bpl
%BGEXE% %* /noVerify TypeDecls1.bpl
%BGEXE% %* /noVerify Prog0.bpl
%BGEXE% %* /noVerify Prog1.bpl
%BGEXE% %* /noVerify Prog2.bpl
%BGEXE% %* /noVerify PolyFuns0.bpl
%BGEXE% %* /noVerify PolyFuns1.bpl
%BGEXE% %* /noVerify PolyProcs0.bpl
%BGEXE% %* /noVerify TypeSynonyms0.bpl
%BGEXE% %* /noVerify TypeSynonyms1.bpl
%BGEXE% %* TypeSynonyms2.bpl
%BGEXE% %* /noVerify /print:- /env:0 TypeSynonyms0.bpl
%BGEXE% %* /noVerify /print:- /env:0 /printDesugared TypeSynonyms2.bpl
%BGEXE% %* /noVerify PolyPolyPoly.bpl
%BGEXE% %* /noVerify PolyPolyPoly2.bpl
%BGEXE% %* /noVerify ProcParamReordering.bpl
%BGEXE% %* /noVerify ParallelAssignment.bpl
%BGEXE% %* /noVerify ParallelAssignment2.bpl
%BGEXE% %* /noVerify Coercions.bpl
%BGEXE% %* /noVerify EmptySeq.bpl
