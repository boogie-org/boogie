// This program is featured in KRML 168, the Marktoberdorf lecture notes
// "A verifying compiler for a multi-threaded object-oriented language" by
// Leino and Schulte.

const K: int;
function f(int) returns (int);
axiom (exists k: int :: f(k) == K);

procedure Find(a: int, b: int) returns (k: int);
  requires a <= b;
  requires (forall j: int :: a < j && j < b ==> f(j) != K);
  ensures f(k) == K;

implementation Find(a: int, b: int) returns (k: int)
{
  entry:
    goto A, B, C;

  A:
    assume f(a) == K;  k := a;
    return;

  B:
    assume f(b) == K;  k := b;
    return;

  C:
    assume f(a) != K && f(b) != K;
    call k := Find(a-1, b+1);
    return;
}

procedure Main() returns (k: int)
  ensures f(k) == K;
{
  entry:
    call k := Find(0, 0);
    return;
}
