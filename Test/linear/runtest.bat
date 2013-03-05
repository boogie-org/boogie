@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (typecheck.bpl list.bpl allocator.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /typeEncoding:m /useArrayTheory /doModSetAnalysis %%f
)

