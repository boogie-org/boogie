@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (houd1.bpl houd2.bpl houd3.bpl houd4.bpl houd5.bpl houd6.bpl houd7.bpl houd8.bpl houd10.bpl houd11.bpl houd12.bpl fail1.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer /printAssignment /abstractHoudini:IA[ConstantProp] %%f
)

for %%f in (test1.bpl test2.bpl test7.bpl test8.bpl test9.bpl test10.bpl) do (
  echo .
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer /printAssignment /inlineDepth:1  /abstractHoudini:IA[ConstantProp] %%f
)

for %%f in (pred1.bpl pred2.bpl pred3.bpl pred4.bpl pred5.bpl) do (
  echo .
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer /printAssignment /inlineDepth:1  /abstractHoudini:PredicateAbs %%f
)

for %%f in (quant1.bpl quant2.bpl quant3.bpl quant4.bpl quant5.bpl) do (
  echo .
  echo -------------------- %%f --------------------
  %BGEXE% %* /nologo /noinfer /contractInfer /printAssignment /abstractHoudini:HoudiniConst /z3opt:MBQI=true %%f
)
