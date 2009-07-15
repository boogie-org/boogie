@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe

for %%f in (arrays.bpl bv0.bpl bv1.bpl bv2.bpl bv3.bpl bv4.bpl bv7.bpl vcc0.bpl) do (
  echo -------------------- %%f --------------------
  %BGEXE% /proverWarnings:1 /bv:z %* /logPrefix:-0 %%f
)

echo -------------------- vcc0.bpl - toInt --------------------
%BGEXE% /proverWarnings:1 /bv:i /proc:foo %* /logPrefix:-1 vcc0.bpl

echo -------------------- bv4.bpl - /bv:n --------------------
%BGEXE% /bv:n %* /logPrefix:-1 bv4.bpl

echo -------------------- bv5.bpl --------------------
%BGEXE% /bv:z %* /logPrefix:-1 bv5.bpl

echo -------------------- bv6.bpl --------------------
%BGEXE% /bv:z %* /logPrefix:-1 bv6.bpl
