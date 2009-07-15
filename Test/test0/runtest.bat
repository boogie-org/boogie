@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

%BGEXE% %* /noVerify Prog0.bpl
%BGEXE% %* /noVerify ModifiedBag.bpl
%BGEXE% %* /noVerify Triggers0.bpl
%BGEXE% %* /noVerify Triggers1.bpl
%BGEXE% %* /noVerify /printInstrumented PrettyPrint.bpl
%BGEXE% %* /noVerify Arrays0.bpl
%BGEXE% %* /noVerify Arrays1.bpl
%BGEXE% %* /noVerify Types0.bpl
%BGEXE% %* /noVerify Types1.bpl
%BGEXE% %* /noVerify WhereParsing.bpl
%BGEXE% %* /noVerify WhereParsing0.bpl
%BGEXE% %* /noVerify WhereParsing1.bpl
%BGEXE% %* /noVerify WhereParsing2.bpl
%BGEXE% %* /noVerify WhereResolution.bpl
%BGEXE% %* /noVerify BadLabels0.bpl
%BGEXE% %* /noVerify BadLabels1.bpl
%BGEXE% %* /noVerify LineParse.bpl
%BGEXE% %* /noVerify LineResolve.bpl
%BGEXE% %* /noVerify AttributeParsingErr.bpl
%BGEXE% %* /noVerify /print:- /env:0 AttributeParsing.bpl
%BGEXE% %* /noVerify AttributeResolution.bpl
%BGEXE% %* /noVerify /print:- /env:0 Quoting.bpl
%BGEXE% %* /noVerify LargeLiterals0.bpl
%BGEXE% %* /noVerify MapsResolutionErrors.bpl
%BGEXE% %* /noVerify Orderings.bpl
%BGEXE% %* /noVerify BadQuantifier.bpl
%BGEXE% %* /noVerify EmptyCallArgs.bpl
