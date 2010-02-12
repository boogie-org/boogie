@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

%BGEXE% %* /noinfer /useArrayTheory bla1.bpl
%BGEXE% %* /noinfer /useArrayTheory daytona_bug2_ioctl_example_1.bpl
%BGEXE% %* /noinfer /useArrayTheory daytona_bug2_ioctl_example_2.bpl
%BGEXE% %* /noinfer /useArrayTheory stack_overflow.bpl

