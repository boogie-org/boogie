// RUN: %boogie -noinfer "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type set a = [a]bool;
function union<T>(a:set T, b:set T) : set T;
axiom (forall<T> a,b:set T :: union(a,b) == (lambda x:T :: a[x] || b[x]));

function diff<T>(a:set T, b:set T) : set T {(lambda x:T :: a[x] && !b[x]) }

procedure a()
{
  var a:set int, b:set int;
  assume a[1];
  assume b[2];
  assert union(a,b)[1];
  assert union(a,b)[2];
  assume !b[1];
  assert diff(a,b)[1];
  assert !diff(a,b)[2];
}

// -----------------------

procedure Polly<Cracker>(c,d: Cracker)
{
  var e: Cracker;
  e := c;

  if (*) {
    assert (forall<T> t: T :: (lambda<beta> b: beta, s: T :: b==c && s==t)[c,t]);
    assert (forall<U> u: U :: (lambda<beta> b: beta, s: U :: b==c && s==u)[u,u]);  // error
  } else if (*) {
    assert (lambda<V> v: V :: (lambda<beta> b: beta, s: V :: b==c && s==v)[v,v])[e];
    assert (lambda<W> w: W :: (lambda<beta> b: beta, s: W :: b==c && s==w)[w,w])[d];  // error
    e := d;
  } else {
    assume TriggerHappy(c);
    assert (exists k: Cracker :: { TriggerHappy(k) } (lambda<beta> b: beta, m: Cracker :: b==k && m==c)[c,c]);
    assert (forall k: Cracker :: (lambda<beta> b: beta, m: Cracker :: b==k && m==c)[c,c]);  // error
  }
}

function TriggerHappy<T>(T): bool;
