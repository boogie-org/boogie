// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Index;
type Permission;

datatype Entry { Entry(permissions: UnitMap (One Permission), x: [One Permission]bool) }

var {:layer 0,1} {:linear} entries: Map (One Index) Entry;

yield invariant {:layer 1} EntryInv(index: Index, {:linear} permission: One Permission);
preserves Map_Contains(entries, One(index));
preserves Set_Contains(Map_At(entries, One(index))->x, permission);
free preserves !Map_Contains(Map_At(entries, One(index))->permissions, permission);

yield procedure {:layer 1} Check(index: Index, {:linear} permission: One Permission)
requires call EntryInv(index, permission);
{
    call CallFoo(index);
}

yield procedure {:layer 0} CallFoo(index: Index);
refines Foo;

atomic action {:layer 1} Foo(index: Index)
modifies entries;
{
    var one_index: One Index;
    var entry: Entry;

    one_index := One(index);
    call entry := Map_Get(entries, one_index);
    assume Set_IsSubset(entry->x, entry->permissions->dom);
}