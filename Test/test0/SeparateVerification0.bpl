// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %boogie -noVerify "%s" "%s" > "%t"
// RUN: %diff NoErrors.expect "%t"
// RUN: %boogie -noVerify "%s" "%s" SeparateVerification1.bpl > "%t"
// RUN: %diff NoErrors.expect "%t"
// need to include this file twice for it to include all necessary declarations

#if FILE_0
const x: int;
#else
const y: int;
#endif

#if FILE_1
axiom x == 12;
procedure Q();
#else
axiom y == 7;
#endif

// duplicates of :extern's are fine (Boogie keeps the non-:extern or chooses arbitrarily among the :extern's)
type {:extern} T;
const {:extern} C: int;
function {:extern} F(): int;
var {:extern} n: int;
procedure {:extern} P(inconsistentParameterButThatIsOkayBecauseTheExternIsIgnored: int);
