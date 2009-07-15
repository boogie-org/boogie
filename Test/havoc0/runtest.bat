@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

%BGEXE% %* /monomorphize KbdCreateClassObject.bpl
%BGEXE% %* /monomorphize KeyboardClassFindMorePorts.bpl
%BGEXE% %* /monomorphize KeyboardClassUnload.bpl
%BGEXE% %* /monomorphize MouCreateClassObject.bpl
%BGEXE% %* /monomorphize MouseClassFindMorePorts.bpl
%BGEXE% %* /monomorphize MouseClassUnload.bpl

