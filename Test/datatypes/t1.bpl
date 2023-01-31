// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type TT;
datatype Tree {
  leaf(), node(value:TT, children:TreeList)
}

datatype TreeList {
  cons(car:Tree, cdr:TreeList), nil()
}

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
