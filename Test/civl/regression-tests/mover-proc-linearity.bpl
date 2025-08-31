// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:linear} g: One int;

yield atomic procedure {:layer 1} A({:linear} a: One int, {:linear} b: One int)
requires {:layer 1} a == b;
{
    assert {:layer 1} false;
}

yield atomic procedure {:layer 1} B({:linear} a: One int)
requires {:layer 1} a == g;
{
    assert {:layer 1} false;
}