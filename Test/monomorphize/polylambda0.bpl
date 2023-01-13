// RUN: %parallel-boogie /monomorphize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Field _;
type Ref;

var f_int: Field int;
var f_bool: Field bool;
var f_field_int: Field (Field int);

function extract<B>(x: Field B, y: int): B;

procedure p(x: Field int) {
    var m2: <B>[Field B]B;
    var i: int;

    m2 := (lambda<B> f: Field B :: extract(f, i));
    assert m2[f_int] == extract(f_int, i);
    assert m2[f_bool] == extract(f_bool, i);
    assert m2[f_field_int] == extract(f_field_int, i);
}