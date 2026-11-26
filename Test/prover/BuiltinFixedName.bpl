// RUN: ! %boogie /prune:1 /proc:CF "%s" > "%t"
// RUN: ! %boogie /prune:1 /proc:TesterOfCF "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Tickle "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Diagnostics /runDiagnosticsOnTimeout "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Coverage /trackVerificationCoverage "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Unbox "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Boogie cannot rename any of these, so claiming one is an error rather than a reservation. With /prune:1 a
// run declares only the functions its procedure uses, so each run reports just its own.

function {:builtin "ControlFlow"} cf(a: int, b: int): int;
procedure CF() { assume (forall a: int, b: int :: cf(a, b) == 0); assert false; }

// Claiming the tester is-ControlFlow would make Boogie rename ControlFlow.
function {:builtin "is-ControlFlow"} tcf(x: int): bool;
procedure TesterOfCF() { assert tcf(0); }

// The blank and the bars still name tickleBool.
function {:builtin " |tickleBool|"} t(b: bool): bool;
procedure Tickle() { assume !t(true); assert false; }

function {:builtin "timeoutDiagnostics"} td(i: int): bool;
procedure Diagnostics() { assume td(0); assert false; }

// The coverage label of the assumption with id a.
function {:builtin "aux$$assume$$a"} b(): bool;
procedure Coverage() { assume {:id "a"} true; assume !b(); assert false; }

// Renaming U_2_int would leave a counterexample's values boxed, so this is an error even under an encoding
// that declares no such function.
function {:builtin "U_2_int"} ui(x: int): int;
procedure Unbox() { assume ui(0) == 0; assert false; }
