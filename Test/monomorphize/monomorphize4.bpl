// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<U> {
  cons(x: U, ls: List U),
  nil()
}

function len<T>(ls: List T): int {
    if (ls == nil()) then 0 else len(cons(ls, nil()))
}
