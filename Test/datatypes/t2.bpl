// RUN: %boogie -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type TT;
type {:datatype} Tree;
function {:constructor} leaf`0() : Tree;
function {:constructor} node`2(value:TT, children:TreeList) : Tree;

type {:datatype} TreeList;
function {:constructor} cons`2(car:Tree, cdr:TreeList) : TreeList;
function {:constructor} nil`0() : TreeList;

procedure foo() 
{
  var a: Tree;
  var b: TreeList;
  var x: TT;

  assert value#node`2(node`2(x, nil`0())) == x;
  assert children#node`2(node`2(x, nil`0())) == nil`0();
  
  assert (cons`2(leaf`0(), nil`0()) != nil`0());

  assert is#nil`0(nil`0());

  assert is#node`2(leaf`0());
}