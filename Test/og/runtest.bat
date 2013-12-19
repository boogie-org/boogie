@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (foo.bpl bar.bpl one.bpl parallel1.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer %%f
)

for %%f in (linear-set.bpl linear-set2.bpl FlanaganQadeer.bpl DeviceCacheSimplified.bpl parallel2.bpl parallel4.bpl parallel5.bpl akash.bpl t1.bpl new1.bpl perm.bpl async.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /typeEncoding:m /useArrayTheory %%f
)

