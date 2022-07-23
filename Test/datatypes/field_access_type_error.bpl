// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure A(a: int);
requires a->f == 0;


type T;
procedure B(a: T);
requires a->f == 0;


type {:datatype} Perm;
function {:constructor} Left(i: int): Perm;
function {:constructor} Right(i: int): Perm;

procedure C(a: Perm);
requires a->f == 0;

procedure D(a: Perm);
requires a->i == 0;
