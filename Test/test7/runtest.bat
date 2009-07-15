@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set BGEXE=%BOOGIEDIR%\Boogie.exe

echo ------------------------------ NestedVC.bpl ---------------------
%BGEXE% %* /vc:nested NestedVC.bpl

echo ------------------------------ UnreachableBlocks.bpl ---------------------
%BGEXE% %* /vc:nested UnreachableBlocks.bpl

echo ------------------------------ MultipleErrors.bpl ---------------------
rem The following tests are rather fickle at the moment--different errors
rem may be reported during different runs.  Moreover, it is conceivable that
rem the error trace would be reported in different orders, since we do not
rem attempt to sort the trace labels at this time.
rem An interesting thing is that /vc:local can with Simplify report more than one
rem error for this file, even with /errorLimit:1.  Other than that, only
rem local and dag produce VCs to which Simplify actually produces different
rem counterexamples.

setlocal
for %%f in (block local dag) do (
  echo.
  echo ----- /vc:%%f
  %BGEXE% %* /errorLimit:1 /errorTrace:1 /vc:%%f /logPrefix:-1%%f MultipleErrors.bpl
)
for %%f in (local dag) do (
  echo.
  echo ----- /errorLimit:10 /vc:%%f
  %BGEXE% %* /errorLimit:10 /errorTrace:1 /vc:%%f /logPrefix:-10%%f MultipleErrors.bpl
)
endlocal
