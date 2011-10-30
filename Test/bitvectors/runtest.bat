@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (arrays.bpl bv0.bpl bv1.bpl bv2.bpl bv3.bpl bv4.bpl bv7.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% /proverWarnings:1 %* %%f
)

for %%f in (bv5.bpl bv6.bpl bv8.bpl bv10.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% %* %%f
)

echo -------------------- bv9.bpl /proverOpt:OPTIMIZE_FOR_BV=true --------------------
%BGEXE% /proverOpt:OPTIMIZE_FOR_BV=true %* bv9.bpl
