// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T;

procedure A(a: int);
requires a->f == 0;
requires a is T;


procedure B(a: T);
requires a->f == 0;
requires a is T;


type {:datatype} Perm;
function {:constructor} Left(i: int): Perm;
function {:constructor} Right(i: int): Perm;

procedure C(a: Perm);
requires a->f == 0;
requires a is Middle;

procedure D(a: Perm);
requires a->i == 0;
