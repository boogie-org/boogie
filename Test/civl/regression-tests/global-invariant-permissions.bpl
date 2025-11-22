// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:layer 0,1} {:linear} usedPermissions: Set (One int);
var {:layer 0,1} g: int;

invariant {:layer 1} Inv();
preserves Set_Contains(usedPermissions, One(0));
preserves g == 0;

yield procedure {:layer 1} Foo()
requires call Inv();
{
}

left action {:layer 1} Blah({:linear} x: One int)
requires call Inv();
{
    assert x->val == 0;
    g := 1;
}