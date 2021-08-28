// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} List _;
function {:constructor} cons<U>(x: U, ls: List U) : List U;
function {:constructor} nil<U>() : List U;

function len<T>(ls: List T): int {
    if (ls == nil()) then 0 else len(cons(ls, nil()))
}
