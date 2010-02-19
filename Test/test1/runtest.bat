@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

%BGEXE% %* /noVerify Frame0.bpl
%BGEXE% %* /noVerify Frame1.bpl
%BGEXE% %* /noVerify LogicalExprs.bpl
%BGEXE% %* /noVerify Arrays.bpl
%BGEXE% %* /noVerify WhereTyping.bpl
%BGEXE% %* /noVerify Family.bpl
%BGEXE% %* /noVerify AttributeTyping.bpl
%BGEXE% %* /noVerify UpdateExprTyping.bpl
%BGEXE% %* /noVerify CallForallResolve.bpl
%BGEXE% %* /noVerify MapsTypeErrors.bpl
%BGEXE% %* /noVerify Orderings.bpl
%BGEXE% %* /noVerify EmptyCallArgs.bpl
%BGEXE% %* /noVerify FunBody.bpl
%BGEXE% %* /noVerify IfThenElse0.bpl
%BGEXE% %* /noVerify Lambda.bpl
