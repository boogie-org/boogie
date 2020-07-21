// RUN: %boogie -inline:spec -print:- -env:0 -printInlined "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type ref;
var arr:[int]int;

procedure {:inline 1} b()
modifies arr;
ensures (forall a:int  :: {arr[a]} a < 10 ==> arr[a] == 0);
{
  assert (forall a:int  :: {arr[a]} a < 10 ==> arr[a] == 0);
}
procedure foo(a:ref)
modifies arr;
{
   call b();
}
