@echo off
setlocal

set BGEXE=..\..\Binaries\Boogie.exe
rem set BGEXE=mono ..\..\Binaries\Boogie.exe

echo ==================== -z3multipleErrors ========================
for %%f in (z3mutl.bpl EQ_v2.Eval__v4.Eval_out.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BGEXE% -typeEncoding:m -z3multipleErrors %* %%f
)

