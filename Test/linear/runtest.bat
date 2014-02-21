@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (typecheck.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /typeEncoding:m /useArrayTheory %%f
)

for %%f in (list.bpl allocator.bpl f1.bpl f2.bpl f3.bpl bug.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /typeEncoding:m /useArrayTheory /doModSetAnalysis %%f
)

