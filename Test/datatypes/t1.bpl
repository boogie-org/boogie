// RUN: %boogie -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type TT;
type {:datatype} Tree;
function {:constructor} leaf() : Tree;
function {:constructor} node(value:TT, children:TreeList) : Tree;

type {:datatype} TreeList;
function {:constructor} cons(car:Tree, cdr:TreeList) : TreeList;
function {:constructor} nil() : TreeList;

procedure foo() 
{
  var a: Tree;
  var b: TreeList;
  var x: TT;

  assert value#node(node(x, nil())) == x;
  assert children#node(node(x, nil())) == nil();
  
  assert (cons(leaf(), nil()) != nil());

  assert is#nil(nil());

  assert is#node(leaf());
}