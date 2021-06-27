// RUN: %boogie -monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:inline 1} A_inline<T>(i: T) returns (j: T) {
    j := i;
}

procedure B_inline(i: int) returns (j: int)
ensures j == i + 1;
{
    call j := A_inline(i);
    j := j + 1;
}

procedure C_inline(i: bool) returns (j: bool)
ensures j == !i;
{
    call j := A_inline(i);
    j := !j;
}

procedure A_spec<T>(i: T) returns (j: T)
ensures j == i;
{
    j := i;
}

procedure B_spec(i: int) returns (j: int)
ensures j == i + 1;
{
    call j := A_spec(i);
    j := j + 1;
}

procedure C_spec(i: bool) returns (j: bool)
ensures j == !i;
{
    call j := A_spec(i);
    j := !j;
}
