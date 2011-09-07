@ECHO OFF

set InputFile=""
set SkeletonFile=""

set ScriptDir=%~p0

:Loop
IF "%1"=="" GOTO Continue

set temp=%1

IF %temp:~0,26%==/generateFormulaSkeletons: GOTO SetSkeletonFile

set InputFile=%1

GOTO LastPartOfLoop

:SetSkeletonFile

set SkeletonFile=%temp:~26%

:LastPartOfLoop

SHIFT
GOTO Loop
:Continue

IF %InputFile%=="" GOTO Error

echo Preprocess
Boogie /noVerify /printUnstructured /print:temp_unstructured.bpl %InputFile% %ScriptDir%..\BoogieLibrary\GPUVerifyLibrary.bpl

IF %SkeletonFile%=="" GOTO Verify

GOTO Generate




:Verify
echo Verify
GPUVerify temp_unstructured.bpl /print:temp_ready_to_verify.bpl
Boogie temp_ready_to_verify.bpl formulas.bpl /prover:smtlib
del temp_unstructured.bpl
GOTO End

:Generate
echo Generate
GPUVerify temp_unstructured.bpl /generateFormulaSkeletons:%SkeletonFile%
del temp_unstructured.bpl
GOTO End

:Error
echo Error: Bad command line specified for GPUVerify
GOTO End




:End