@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (test0.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% %* %%f
)

for %%f in (test1.bpl test2.bpl test3.bpl test4.bpl test6.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% %* /inline:spec /print:- /env:0 /printInlined /noinfer %%f
)

for %%f in (test5.bpl expansion.bpl expansion3.bpl Elevator.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% %* %%f
)

REM Peephole optimizations are so good that Elevator seems worthwhile
REM to include twice among these inline tests
for %%f in (Elevator.bpl) do (
  echo -------------------- %%f with empty blocks --------------------
  %BGEXE% /removeEmptyBlocks:0 %* %%f
)

echo -------------------- expansion2.bpl --------------------
%BGEXE% %* /proverLog:expansion2.sx expansion2.bpl
%SystemRoot%\system32\find.exe /C "xxgz" expansion2.sx
%SystemRoot%\system32\find.exe /C "xxf1" expansion2.sx

echo -------------------- expansion4.bpl --------------------
%BGEXE% %* /bv:i expansion4.bpl

echo -------------------- fundef.bpl --------------------
%BGEXE% %* /print:- /env:0 fundef.bpl
%BGEXE% %* fundef2.bpl

echo -------------------- polyInline.bpl --------------------
%BGEXE% %* /typeEncoding:predicates /logPrefix:p polyInline.bpl
%BGEXE% %* /typeEncoding:arguments /logPrefix:a polyInline.bpl
