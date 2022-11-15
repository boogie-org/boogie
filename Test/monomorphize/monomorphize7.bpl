// RUN: %parallel-boogie -lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:inline} $Box(x: $Value): $Value {
    x
}
function {:inline} $Box_int(x: int): $Value {
    $Integer(x)
}
function {:inline} $Box_bool(x: bool): $Value {
    $Boolean(x)
}
function {:inline} $Box_addr(x: int): $Value {
    $Address(x)
}
function {:inline} $Box_vec(x: Vec $Value): $Value {
    $Vector(x)
}

function {:inline} $Unbox(x: $Value): $Value {
    x
}
function {:inline} $Unbox_int(x: $Value): int {
    x->i
}
function {:inline} $Unbox_bool(x: $Value): bool {
    x->b
}
function {:inline} $Unbox_addr(x: $Value): int {
    x->a
}
function {:inline} $Unbox_vec(x: $Value): Vec $Value {
    x->v
}

type {:datatype} $Value;
function {:constructor} $Boolean(b: bool): $Value;
function {:constructor} $Integer(i: int): $Value;
function {:constructor} $Address(a: int): $Value;
function {:constructor} $Vector(v: Vec $Value): $Value;
function {:constructor} $Error(): $Value;

procedure p() {
    assert $Unbox_vec($Box_vec(Vec_Empty())) == Vec_Empty();
}
