// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<U> {
  cons(x: U, ls: List U),
  nil()
}

function len<T>(ls: List T): int {
    if (ls == nil()) then 0 else 1 + len(ls->ls)
}

type X;
procedure find_length_X(ls: List X) returns (length: int)
ensures length == len(ls);
{
    if (ls == nil()) {
        length := 0;
    } else {
        call length := find_length_X(ls->ls);
        length := length + 1;
    }
}

procedure find_length_int(ls: List int) returns (length: int)
ensures length == len(ls);
{
    if (ls == nil()) {
        length := 0;
    } else {
        call length := find_length_int(ls->ls);
        length := length + 1;
    }
}
