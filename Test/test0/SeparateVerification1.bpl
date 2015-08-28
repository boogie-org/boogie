// RUN: %boogie -noVerify "%s" SeparateVerification0.bpl > "%t"
// RUN: %diff "%s.expect" "%t"
// to be used with SeparateVerification0.bpl

// x and y are declared in SeparateVerification0.bpl
axiom x + y <= 100;

// these are declared as :extern as SeparateVerification0.bpl
type T;
const C: int;
function F(): int;
var n: int;
procedure P();
procedure {:extern} Q(x: int);

procedure Main() {
  call P();  // note, calling the parameter-less non-extern P (an extern and a non-extern
             // declaration of the same name are usually mostly identical declarations,
             // but Boogie allows them to be different, because it ignores the extern ones)
  call Q();  // ditto
}
