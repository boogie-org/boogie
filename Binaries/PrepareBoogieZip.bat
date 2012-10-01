@echo off
setlocal

set DEST_DIR=export

if exist %DEST_DIR% del /q %DEST_DIR%\*
if not exist %DEST_DIR% mkdir %DEST_DIR%

for %%f in (
  AbsInt.dll                          AbsInt.pdb
  Basetypes.dll                       Basetypes.pdb
  Boogie.exe                          Boogie.pdb
  CodeContractsExtender.dll           CodeContractsExtender.pdb
  Core.dll                            Core.pdb
  Dafny.exe                           Dafny.pdb
  DafnyPrelude.bpl                    DafnyRuntime.cs
  DafnyPipeline.dll                   DafnyPipeline.pdb
  Graph.dll                           Graph.pdb
  Houdini.dll
  Model.dll                           Model.pdb
  ParserHelper.dll                    ParserHelper.pdb
  Provers.SMTLib.dll                  Provers.SMTLib.pdb
  TypedUnivBackPred2.sx
  UnivBackPred2.smt                   UnivBackPred2.smt2
  UnivBackPred2.sx
  VCExpr.dll                          VCExpr.pdb
  VCGeneration.dll                    VCGeneration.pdb
) do (
  copy %%f %DEST_DIR%
)

xcopy /E /I /Y CodeContracts "%DEST_DIR%/CodeContracts"

echo Done.  Now, manually put the contents of the %DEST_DIR% directory into Boogie.zip
