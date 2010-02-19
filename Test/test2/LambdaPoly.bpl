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

