@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (foo.bpl bar.bpl one.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /doModSetAnalysis /OwickiGries:OwickiGriesDesugared.bpl %%f
)

for %%f in (linear-set.bpl linear-set2.bpl FlanaganQadeer.bpl DeviceCacheSimplified.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /typeEncoding:m /useArrayTheory /doModSetAnalysis  /OwickiGries:OwickiGriesDesugared.bpl %%f Maps.bpl
)

