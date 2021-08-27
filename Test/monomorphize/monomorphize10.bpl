// RUN: %parallel-boogie -monomorphize "%s" > "%t"
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

procedure D(i: int, b: bool) returns (j: int, c: bool)
ensures i == j;
ensures b == c;
{
    call j := A_inline(i);
    call j := A_spec(j);
    call c := A_inline(b);
    call c := A_spec(c);
}

procedure {:inline 1} AA_inline<T, U>(x: T, y: U) returns (z: T, w: U) {
    z := x;
    w := y;
}

procedure AA_spec<T, U>(x: T, y: U) returns (z: T, w: U)
ensures z == x;
ensures w == y;
{
    z := x;
    w := y;
}

procedure DD(i: int, b: bool) returns (j: int, c: bool)
ensures i == j;
ensures b == c;
{
    call j, c := AA_inline(i, b);
    call j, c := AA_spec(j, c);
}

procedure E<T>(i: T, b: bool) returns (j: T, c: bool)
ensures i == j;
ensures b == c;
{
    call j, c := AA_inline(i, b);
    call j, c := AA_spec(j, c);
}

procedure A_no_body<T>(i: T) returns (j: T);
ensures j == i;

procedure DDD(i: int, b: bool) returns (j: int, c: bool)
ensures i == j;
ensures b == c;
{
    call j := A_inline(i);
    call j := A_no_body(j);
    call c := A_inline(b);
    call c := A_no_body(c);
}

procedure A_wrapper<T>(i: T) returns (j: T)
ensures j == i;
{
    call j := A_no_body(i);
}
