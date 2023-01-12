// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Field _;
type Ref;

var f_int: Field int;
var f_bool: Field bool;
var f_field_int: Field (Field int);

procedure p(x: Field int) {
    var m2: <B>[Field B]B;
    var m1: [Ref](<B>[Field B]B);
    var r: Ref;

    assume m1[r] == m2;
    assume m2[f_int] == 5;
    assume m2[f_bool] == true;
    assume m2[f_field_int] == f_int;

    assert m2[f_int] > 0;
    assert m2[f_bool];
    assert m2[f_field_int] == f_int;
    assert m1[r] == m2;
}