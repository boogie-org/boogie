// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List1 { List1(data: int, next: List1) }

datatype List2 { List2(data: int, next: [int]List2) }

datatype Foo { Foo(l: List3) }

datatype List3 { List3(data: int, f: Foo) }

datatype List4 { List4(l: List2) }