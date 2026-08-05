// RUN: %boogie -noVerify -print:- -env:0 -printDesugared "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// "+" and "*" are printed left-associatively, so the parentheses of "x + (y + z)" may
// only be dropped when "(x + y) + z" is the same expression:
//   - on int and real, "+" regroups with "+" and "-", and "*" regroups with "*";
//   - "i * (j div k)" keeps its parentheses, since "i * j div k" is "(i * j) div k";
//   - floating-point "+" and "*" are not associative, so "x + (y + z)" keeps its
//     parentheses even though the operator matches.
// Before typechecking no type is known, so everything is parenthesized (first printout).
procedure main() returns () {
  var i, j, k: int;
  var r, s, t: real;
  var x, y, z: float24e8;

  // associative type, regrouping operator: parentheses may be dropped
  i := i + (j + k);
  i := i * (j * k);
  r := r + (s + t);
  r := r * (s * t);
  i := i + (j - k);

  // same precedence, but truncating or undefined at zero: parentheses must stay
  i := i * (j div k);
  i := i * (j mod k);
  r := r * (s / t);

  // non-associative type: parentheses must stay
  x := x + (y + z);
  x := x * (y * z);
  x := x + (y - z);
  x := x * (y / z);
}
