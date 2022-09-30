// RUN: %parallel-boogie "%s" > "%t"
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

  assert node(x, nil())->value == x;
  assert node(x, nil())->children == nil();

  assert (cons(leaf(), nil()) != nil());

  assert nil() is nil;

  assert leaf() is node;
}
