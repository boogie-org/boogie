@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (arrays.bpl bv0.bpl bv1.bpl bv2.bpl bv3.bpl bv4.bpl bv7.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% /proverWarnings:1 /bv:z %* /logPrefix:-0 %%f
)

echo -------------------- bv4.bpl - /bv:n --------------------
%BGEXE% /bv:n %* /logPrefix:-1 bv4.bpl

for %%f in (bv5.bpl bv6.bpl bv8.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% %* %%f
)
