@echo off
setlocal

set DEST_DIR=export

if exist %DEST_DIR% del /q %DEST_DIR%\*
if not exist %DEST_DIR% mkdir %DEST_DIR%

for %%f in (
  AbsInt.dll                          AbsInt.pdb
  Basetypes.dll                       Basetypes.pdb
  Boogie.exe                          Boogie.pdb
  BVD.exe                             BVD.pdb
  CodeContractsExtender.dll           CodeContractsExtender.pdb
  Core.dll                            Core.pdb
  Doomed.dll                          Doomed.pdb
  Graph.dll                           Graph.pdb
  Houdini.dll                         Houdini.pdb
  Model.dll                           Model.pdb
  ParserHelper.dll                    ParserHelper.pdb
  Predication.dll                     Predication.pdb
  Provers.SMTLib.dll                  Provers.SMTLib.pdb
  UnivBackPred2.smt                   UnivBackPred2.smt2
  VCExpr.dll                          VCExpr.pdb
  VCGeneration.dll                    VCGeneration.pdb
) do (
  copy %%f %DEST_DIR%
)

xcopy /E /I /Y CodeContracts "%DEST_DIR%/CodeContracts"

echo Done.  Now, manually put the contents of the %DEST_DIR% directory into Boogie.zip
