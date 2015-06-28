// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function in_set(int) returns(bool);
function next(int) returns(int);
function f(int) returns(bool);
function g(int) returns(bool);

// this function is treated specially by Z3 when used in triggers
//    sk_hack(f(x)) means to activate the e-node f(x0) when trying to prove
//    !(forall x : T :: {sk_hack(f(x))} p(x)) by proving !p(x0) 
//    (i.e., after skolemization of x to x0).
function sk_hack(bool) returns(bool);

// PR: sk_hack cannot be defined as a polymorphic function
// when using /quantifierTypePremisses:a, because then it would
// get an additional explicit type parameter, and Z3 would
// no longer recognise it.

procedure foo()
{
  assume (forall x:int :: {in_set(next(x))}
     in_set(x) ==> in_set(next(x)));

  assume (forall x:int :: {in_set(x)}
     in_set(x) ==> f(x));

  assume (forall x:int :: {f(next(x))}
     f(next(x)) ==> g(x));

  assert (forall x:int ::
    { sk_hack(in_set(next(x))) }
    in_set(x) ==> g(x));
  }

