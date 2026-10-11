// RUN: ! %boogie /prune:1 /proc:CF "%s" > "%t"
// RUN: ! %boogie /prune:1 /proc:TesterOfCF "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Tickle "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Diagnostics /runDiagnosticsOnTimeout "%s" >> "%t"
// RUN: ! %boogie /prune:1 /proc:Coverage /trackVerificationCoverage "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Boogie constrains these symbols, or reads them back, under fixed names, so none of them can step aside for a
// {:builtin} function. With /prune:1, a run declares only the functions its procedure uses.

function {:builtin "ControlFlow"} cf(a: int, b: int): int;
procedure CF() { assume (forall a: int, b: int :: cf(a, b) == 0); assert false; }

// The tester is-ControlFlow would move ControlFlow.
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
