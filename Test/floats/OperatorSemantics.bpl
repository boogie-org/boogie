// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Each float operator means the SMT-LIB term that the comment on FloatType gives.

function {:builtin "="} eq(float24e8, float24e8) returns (bool);
function {:builtin "fp.lt"} fpLt(float24e8, float24e8) returns (bool);
function {:builtin "fp.leq"} fpLeq(float24e8, float24e8) returns (bool);
function {:builtin "fp.gt"} fpGt(float24e8, float24e8) returns (bool);
function {:builtin "fp.geq"} fpGeq(float24e8, float24e8) returns (bool);
function {:builtin "fp.add"} fpAdd(rmode, float24e8, float24e8) returns (float24e8);
function {:builtin "fp.sub"} fpSub(rmode, float24e8, float24e8) returns (float24e8);
function {:builtin "fp.mul"} fpMul(rmode, float24e8, float24e8) returns (float24e8);
function {:builtin "fp.div"} fpDiv(rmode, float24e8, float24e8) returns (float24e8);

procedure Eq(x: float24e8, y: float24e8) { assert (x == y) == eq(x, y); }
procedure Neq(x: float24e8, y: float24e8) { assert (x != y) == !eq(x, y); }
procedure Lt(x: float24e8, y: float24e8) { assert (x < y) == fpLt(x, y); }
procedure Le(x: float24e8, y: float24e8) { assert (x <= y) == fpLeq(x, y); }
procedure Gt(x: float24e8, y: float24e8) { assert (x > y) == fpGt(x, y); }
procedure Ge(x: float24e8, y: float24e8) { assert (x >= y) == fpGeq(x, y); }
procedure Add(x: float24e8, y: float24e8) { assert eq(x + y, fpAdd(RNE, x, y)); }
procedure Sub(x: float24e8, y: float24e8) { assert eq(x - y, fpSub(RNE, x, y)); }
procedure Mul(x: float24e8, y: float24e8) { assert eq(x * y, fpMul(RNE, x, y)); }
procedure Div(x: float24e8, y: float24e8) { assert eq(x / y, fpDiv(RNE, x, y)); }
