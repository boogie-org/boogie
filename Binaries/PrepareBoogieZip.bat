@echo off
setlocal

set DEST_DIR=export

if exist %DEST_DIR% del /q %DEST_DIR%\*
if not exist %DEST_DIR% mkdir %DEST_DIR%

for %%f in (
  BoogieAbsInt.dll                          BoogieAbsInt.pdb
  BoogieBasetypes.dll                       BoogieBasetypes.pdb
  Boogie.exe                                Boogie.pdb
  BVD.exe                                   BVD.pdb
  BoogieCodeContractsExtender.dll           BoogieCodeContractsExtender.pdb
  BoogieCore.dll                            BoogieCore.pdb
  BoogieDoomed.dll                          BoogieDoomed.pdb
  BoogieGraph.dll                           BoogieGraph.pdb
  BoogieHoudini.dll                         BoogieHoudini.pdb
  BoogieModel.dll                           BoogieModel.pdb
  BoogieParserHelper.dll                    BoogieParserHelper.pdb
  BoogiePredication.dll                     BoogiePredication.pdb
  Provers.SMTLib.dll                        Provers.SMTLib.pdb
  UnivBackPred2.smt                         UnivBackPred2.smt2
  BoogieVCExpr.dll                          BoogieVCExpr.pdb
  BoogieVCGeneration.dll                    BoogieVCGeneration.pdb
) do (
  copy %%f %DEST_DIR%
)

xcopy /E /I /Y CodeContracts "%DEST_DIR%/CodeContracts"

echo Done.  Now, manually put the contents of the %DEST_DIR% directory into Boogie.zip
