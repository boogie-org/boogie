// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

yield procedure {:layer 1} foo1({:linear} x: One int, {:linear} y: One int)
{
    assert {:layer 1} x != y;
}
