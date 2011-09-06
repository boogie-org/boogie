echo off

Boogie /noVerify /printUnstructured /print:temp_instrumented.bpl %1 %~p0..\BoogieLibrary\GPUVerifyLibrary.bpl

GPUVerify temp_unstructured.bpl /print:temp_ready_to_verify.bpl

Boogie temp_ready_to_verify.bpl /prover:smtlib

del temp_instrumented.bpl
