// RUN: %boogie -noVerify -print:- -env:0 -printDesugared "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// "+" and "*" print left-associatively, so "x + (y + z)" may lose its parentheses only
// where "(x + y) + z" is the same expression:
//   - on int and real, "+" regroups with "+" and "-", and "*" with "*";
//   - "i * j div k" is "(i * j) div k", so "i * (j div k)" keeps its parentheses;
//   - float "+" and "*" are not associative, so they keep theirs even when the
//     operator matches.
// The first printout is pre-typecheck, where no type is known and nothing regroups.
procedure main() returns () {
  var i, j, k: int;
  var r, s, t: real;
  var x, y, z: float24e8;

  // regroups: parentheses may be dropped
  i := i + (j + k);
  i := i * (j * k);
  r := r + (s + t);
  r := r * (s * t);
  i := i + (j - k);

  // truncating or undefined at zero: parentheses stay
  i := i * (j div k);
  i := i * (j mod k);
  r := r * (s / t);

  // float: parentheses stay
  x := x + (y + z);
  x := x * (y * z);
  x := x + (y - z);
  x := x * (y / z);
}
