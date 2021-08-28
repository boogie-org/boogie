// RUN: %parallel-boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type {:datatype} List _;
function {:constructor} cons<U>(x: U, ls: List U) : List U;
function {:constructor} nil<U>() : List U;

function len<T>(ls: List T): int {
    if (ls == nil()) then 0 else 1 + len(ls#cons(ls))
}

type X;
procedure find_length_X(ls: List X) returns (length: int)
ensures length == len(ls);
{
    if (ls == nil()) {
        length := 0;
    } else {
        call length := find_length_X(ls#cons(ls));
        length := length + 1;
    }
}

procedure find_length_int(ls: List int) returns (length: int)
ensures length == len(ls);
{
    if (ls == nil()) {
        length := 0;
    } else {
        call length := find_length_int(ls#cons(ls));
        length := length + 1;
    }
}
