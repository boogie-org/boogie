@echo off
setlocal

set DEST_DIR=export

if exist %DEST_DIR% del /q %DEST_DIR%\*
if not exist %DEST_DIR% mkdir %DEST_DIR%

for %%f in (
  AbsInt.dll            AbsInt.pdb
  AIFramework.dll       AIFramework.pdb
  Basetypes.dll         Basetypes.pdb
  Boogie.exe            Boogie.pdb
  Core.dll              Core.pdb
  Dafny.exe             Dafny.pdb
  DafnyPipeline.dll     DafnyPipeline.pdb
  Graph.dll             Graph.pdb
  Provers.Isabelle.dll  Provers.Isabelle.pdb
  Provers.SMTLib.dll    Provers.SMTLib.pdb
  Provers.Simplify.dll  Provers.Simplify.pdb
  Provers.Z3.dll        Provers.Z3.pdb
  VCExpr.dll            VCExpr.pdb
  VCGeneration.dll      VCGeneration.pdb
  DafnyPrelude.bpl
  DafnyRuntime.cs
  TypedUnivBackPred2.sx
  UnivBackPred2.smt
  UnivBackPred2.sx
  FSharp.Core.dll
  FSharp.PowerPack.dll
  Microsoft.SpecSharp.Runtime.dll
  Microsoft.SpecSharp.dll
  System.Compiler.Framework.dll
  System.Compiler.Runtime.dll
  System.Compiler.dll
) do (
  copy %%f %DEST_DIR%
)

echo Done.  Now, manually put the contents of the %DEST_DIR% directory into Boogie.zip
