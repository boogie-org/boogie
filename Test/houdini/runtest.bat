@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (houd1.bpl houd2.bpl houd3.bpl houd4.bpl houd5.bpl houd6.bpl houd7.bpl houd8.bpl houd9.bpl houd10.bpl houd11.bpl houd12.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer %%f
)

for %%f in (test7.bpl test8.bpl) do (
  echo .
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer /inline:spec /inlineDepth:1 %%f
)
