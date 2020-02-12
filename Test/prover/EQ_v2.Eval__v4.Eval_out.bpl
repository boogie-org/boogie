// RUN: %boogie -typeEncoding:m -z3multipleErrors "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var v4.Mem: [name][int]int;

var v4.alloc: int;

var v4.Mem_T.INT4: [int]int;

var v4.Mem_T.op1__EXPR: [int]int;

var v4.Mem_T.op2__EXPR: [int]int;

var v4.Mem_T.oper__EXPR: [int]int;

var v4.Mem_T.result__EXPR: [int]int;

var v4.detChoiceCnt: int;

var v4.Res_KERNEL_SOURCE: [int]int;

var v4.Res_PROBED: [int]int;

var v4.isUnsigned: int;

const unique v4.T.oper__EXPR: name;

const unique v4.T.op1__EXPR: name;

const unique v4.T.op2__EXPR: name;

const unique v4.T.result__EXPR: name;

const unique v4.T.INT4: name;

const unique v4.T.PINT4: name;

const unique v4.T.PPINT4: name;

const unique v4.T.PP_EXPR: name;

const unique v4.T.P_EXPR: name;

const unique v4.T._EXPR: name;

const {:model_const "e->op2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 23} unique v4.__ctobpl_const_9: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 24} unique v4.__ctobpl_const_10: int;

const {:model_const "op"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 26} unique v4.__ctobpl_const_11: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 41} unique v4.__ctobpl_const_12: int;

const {:model_const "e->op1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 22} unique v4.__ctobpl_const_6: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 23} unique v4.__ctobpl_const_7: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 23} unique v4.__ctobpl_const_8: int;

const {:model_const "e->oper"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 21} unique v4.__ctobpl_const_3: int;

const {:model_const "op"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 21} unique v4.__ctobpl_const_1: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 21} unique v4.__ctobpl_const_2: int;

const {:model_const "e->result"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 41} unique v4.__ctobpl_const_13: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 41} unique v4.__ctobpl_const_14: int;

const {:model_const "isUnsigned"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 29} unique v4.__ctobpl_const_15: int;

const {:model_const "isUnsigned"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 35} unique v4.__ctobpl_const_16: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 38} unique v4.__ctobpl_const_17: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 38} unique v4.__ctobpl_const_18: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 38} unique v4.__ctobpl_const_19: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 36} unique v4.__ctobpl_const_20: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 36} unique v4.__ctobpl_const_21: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 36} unique v4.__ctobpl_const_22: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 36} unique v4.__ctobpl_const_23: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 36} unique v4.__ctobpl_const_24: int;

const {:model_const "result.UnsignedSub"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 36} unique v4.__ctobpl_const_25: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 32} unique v4.__ctobpl_const_26: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 32} unique v4.__ctobpl_const_27: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 32} unique v4.__ctobpl_const_28: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 30} unique v4.__ctobpl_const_29: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 30} unique v4.__ctobpl_const_30: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 30} unique v4.__ctobpl_const_31: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 30} unique v4.__ctobpl_const_32: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 30} unique v4.__ctobpl_const_33: int;

const {:model_const "result.UnsignedAdd"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 30} unique v4.__ctobpl_const_34: int;

const {:model_const "isUnsigned"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 47} unique v4.__ctobpl_const_35: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 22} unique v4.__ctobpl_const_4: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 22} unique v4.__ctobpl_const_5: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 48} unique v4.__ctobpl_const_36: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 48} unique v4.__ctobpl_const_37: int;

const {:model_const "outval"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 49} unique v4.__ctobpl_const_38: int;

const {:model_const "*outval"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 49} unique v4.__ctobpl_const_39: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 49} unique v4.__ctobpl_const_40: int;

const {:model_const "e->result"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 49} unique v4.__ctobpl_const_41: int;

const {:model_const "isUnsigned"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 54} unique v4.__ctobpl_const_42: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 55} unique v4.__ctobpl_const_43: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceLine 55} unique v4.__ctobpl_const_44: int;

function v4.OneByteToInt(arg_0: byte) : int;

function v4.TwoBytesToInt(arg_0: byte, arg_1: byte) : int;

function v4.FourBytesToInt(arg_0: byte, arg_1: byte, arg_2: byte, arg_3: byte) : int;

function v4.Field(arg_0: int) : name;

function v4.Base(arg_0: int) : int;

function v4.Match(a: int, t: name) : bool;

function v4.MatchBase(b: int, a: int, t: name) : bool;

function v4.HasType(v: int, t: name) : bool;

function v4.T.Ptr(t: name) : name;

function v4.op1__EXPR(arg_0: int) : int;

function v4.op1__EXPRInv(arg_0: int) : int;

function v4._S_op1__EXPR(arg_0: [int]bool) : [int]bool;

function v4._S_op1__EXPRInv(arg_0: [int]bool) : [int]bool;

function v4.op2__EXPR(arg_0: int) : int;

function v4.op2__EXPRInv(arg_0: int) : int;

function v4._S_op2__EXPR(arg_0: [int]bool) : [int]bool;

function v4._S_op2__EXPRInv(arg_0: [int]bool) : [int]bool;

function v4.oper__EXPR(arg_0: int) : int;

function v4.oper__EXPRInv(arg_0: int) : int;

function v4._S_oper__EXPR(arg_0: [int]bool) : [int]bool;

function v4._S_oper__EXPRInv(arg_0: [int]bool) : [int]bool;

function v4.result__EXPR(arg_0: int) : int;

function v4.result__EXPRInv(arg_0: int) : int;

function v4._S_result__EXPR(arg_0: [int]bool) : [int]bool;

function v4._S_result__EXPRInv(arg_0: [int]bool) : [int]bool;

function v4.INT_EQ(x: int, y: int) : bool;

function v4.INT_NEQ(x: int, y: int) : bool;

function v4.INT_ADD(x: int, y: int) : int;

function v4.INT_SUB(x: int, y: int) : int;

function v4.INT_MULT(x: int, y: int) : int;

function v4.INT_DIV(x: int, y: int) : int;

function v4.INT_LT(x: int, y: int) : bool;

function v4.INT_ULT(x: int, y: int) : bool;

function v4.INT_LEQ(x: int, y: int) : bool;

function v4.INT_ULEQ(x: int, y: int) : bool;

function v4.INT_GT(x: int, y: int) : bool;

function v4.INT_UGT(x: int, y: int) : bool;

function v4.INT_GEQ(x: int, y: int) : bool;

function v4.INT_UGEQ(x: int, y: int) : bool;

function v4.BV32_EQ(x: bv32, y: bv32) : bool;

function v4.BV32_NEQ(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvadd"} v4.BV32_ADD(x: bv32, y: bv32) : bv32;

function {:bvbuiltin "bvsub"} v4.BV32_SUB(x: bv32, y: bv32) : bv32;

function {:bvbuiltin "bvmul"} v4.BV32_MULT(x: bv32, y: bv32) : bv32;

function {:bvbuiltin "bvudiv"} v4.BV32_DIV(x: bv32, y: bv32) : bv32;

function {:bvbuiltin "bvult"} v4.BV32_ULT(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvslt"} v4.BV32_LT(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvule"} v4.BV32_ULEQ(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvsle"} v4.BV32_LEQ(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvugt"} v4.BV32_UGT(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvsgt"} v4.BV32_GT(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvuge"} v4.BV32_UGEQ(x: bv32, y: bv32) : bool;

function {:bvbuiltin "bvsge"} v4.BV32_GEQ(x: bv32, y: bv32) : bool;

function v4.MINUS_BOTH_PTR_OR_BOTH_INT(a: int, b: int, size: int) : int;

function v4.MINUS_LEFT_PTR(a: int, a_size: int, b: int) : int;

function v4.PLUS(a: int, a_size: int, b: int) : int;

function v4.MULT(a: int, b: int) : int;

function v4.DIV(a: int, b: int) : int;

function v4.BINARY_BOTH_INT(a: int, b: int) : int;

function v4.POW2(a: int) : bool;

function v4.BIT_BAND(a: int, b: int) : int;

function v4.BIT_BOR(a: int, b: int) : int;

function v4.BIT_BXOR(a: int, b: int) : int;

function v4.BIT_BNOT(a: int) : int;

function v4.choose(a: bool, b: int, c: int) : int;

function v4.LIFT(a: bool) : int;

function v4.PTR_NOT(a: int) : int;

function v4.NULL_CHECK(a: int) : int;

function v4.NewAlloc(x: int, y: int) : int;

function v4.DetChoiceFunc(a: int) : int;

function v4.Equal(arg_0: [int]bool, arg_1: [int]bool) : bool;

function v4.Subset(arg_0: [int]bool, arg_1: [int]bool) : bool;

function v4.Disjoint(arg_0: [int]bool, arg_1: [int]bool) : bool;

function v4.Empty() : [int]bool;

function v4.SetTrue() : [int]bool;

function v4.Singleton(arg_0: int) : [int]bool;

function v4.Reachable(arg_0: [int,int]bool, arg_1: int) : [int]bool;

function v4.Union(arg_0: [int]bool, arg_1: [int]bool) : [int]bool;

function v4.Intersection(arg_0: [int]bool, arg_1: [int]bool) : [int]bool;

function v4.Difference(arg_0: [int]bool, arg_1: [int]bool) : [int]bool;

function v4.Dereference(arg_0: [int]bool, arg_1: [int]int) : [int]bool;

function v4.Inverse(f: [int]int, x: int) : [int]bool;

function v4.AtLeast(arg_0: int, arg_1: int) : [int]bool;

function v4.Rep(arg_0: int, arg_1: int) : int;

function v4.Array(arg_0: int, arg_1: int, arg_2: int) : [int]bool;

function v4.Unified(arg_0: [name][int]int) : [int]int;

function v4.value_is(c: int, e: int) : bool;

axiom (forall b0: byte, c0: byte :: { v4.OneByteToInt(b0), v4.OneByteToInt(c0) } v4.OneByteToInt(b0) == v4.OneByteToInt(c0) ==> b0 == c0);

axiom (forall b0: byte, b1: byte, c0: byte, c1: byte :: { v4.TwoBytesToInt(b0, b1), v4.TwoBytesToInt(c0, c1) } v4.TwoBytesToInt(b0, b1) == v4.TwoBytesToInt(c0, c1) ==> b0 == c0 && b1 == c1);

axiom (forall b0: byte, b1: byte, b2: byte, b3: byte, c0: byte, c1: byte, c2: byte, c3: byte :: { v4.FourBytesToInt(b0, b1, b2, b3), v4.FourBytesToInt(c0, c1, c2, c3) } v4.FourBytesToInt(b0, b1, b2, b3) == v4.FourBytesToInt(c0, c1, c2, c3) ==> b0 == c0 && b1 == c1 && b2 == c2 && b3 == c3);

axiom (forall x: int :: { v4.Base(x) } v4.INT_LEQ(v4.Base(x), x));

axiom (forall a: int, t: name :: { v4.Match(a, v4.T.Ptr(t)) } v4.Match(a, v4.T.Ptr(t)) <==> v4.Field(a) == v4.T.Ptr(t));

axiom (forall b: int, a: int, t: name :: { v4.MatchBase(b, a, v4.T.Ptr(t)) } v4.MatchBase(b, a, v4.T.Ptr(t)) <==> v4.Base(a) == b);

axiom (forall v: int, t: name :: { v4.HasType(v, v4.T.Ptr(t)) } v4.HasType(v, v4.T.Ptr(t)) <==> v == 0 || (v4.INT_GT(v, 0) && v4.Match(v, t) && v4.MatchBase(v4.Base(v), v, t)));

axiom (forall x: int, S: [int]bool :: { v4._S_op1__EXPR(S)[x] } v4._S_op1__EXPR(S)[x] <==> S[v4.op1__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_op1__EXPRInv(S)[x] } v4._S_op1__EXPRInv(S)[x] <==> S[v4.op1__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op1__EXPR(S) } S[x] ==> v4._S_op1__EXPR(S)[v4.op1__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op1__EXPRInv(S) } S[x] ==> v4._S_op1__EXPRInv(S)[v4.op1__EXPRInv(x)]);

axiom (forall x: int :: { v4.op1__EXPR(x) } v4.op1__EXPR(x) == v4.INT_ADD(x, 4));

axiom (forall x: int :: { v4.op1__EXPRInv(x) } v4.op1__EXPRInv(x) == v4.INT_SUB(x, 4));

axiom (forall x: int :: { v4.op1__EXPR(x) } v4.op1__EXPR(x) == v4.PLUS(x, 1, 4));

axiom (forall x: int, S: [int]bool :: { v4._S_op2__EXPR(S)[x] } v4._S_op2__EXPR(S)[x] <==> S[v4.op2__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_op2__EXPRInv(S)[x] } v4._S_op2__EXPRInv(S)[x] <==> S[v4.op2__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op2__EXPR(S) } S[x] ==> v4._S_op2__EXPR(S)[v4.op2__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op2__EXPRInv(S) } S[x] ==> v4._S_op2__EXPRInv(S)[v4.op2__EXPRInv(x)]);

axiom (forall x: int :: { v4.op2__EXPR(x) } v4.op2__EXPR(x) == v4.INT_ADD(x, 8));

axiom (forall x: int :: { v4.op2__EXPRInv(x) } v4.op2__EXPRInv(x) == v4.INT_SUB(x, 8));

axiom (forall x: int :: { v4.op2__EXPR(x) } v4.op2__EXPR(x) == v4.PLUS(x, 1, 8));

axiom (forall x: int, S: [int]bool :: { v4._S_oper__EXPR(S)[x] } v4._S_oper__EXPR(S)[x] <==> S[v4.oper__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_oper__EXPRInv(S)[x] } v4._S_oper__EXPRInv(S)[x] <==> S[v4.oper__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_oper__EXPR(S) } S[x] ==> v4._S_oper__EXPR(S)[v4.oper__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_oper__EXPRInv(S) } S[x] ==> v4._S_oper__EXPRInv(S)[v4.oper__EXPRInv(x)]);

axiom (forall x: int :: { v4.oper__EXPR(x) } v4.oper__EXPR(x) == v4.INT_ADD(x, 0));

axiom (forall x: int :: { v4.oper__EXPRInv(x) } v4.oper__EXPRInv(x) == v4.INT_SUB(x, 0));

axiom (forall x: int :: { v4.oper__EXPR(x) } v4.oper__EXPR(x) == v4.PLUS(x, 1, 0));

axiom (forall x: int, S: [int]bool :: { v4._S_result__EXPR(S)[x] } v4._S_result__EXPR(S)[x] <==> S[v4.result__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_result__EXPRInv(S)[x] } v4._S_result__EXPRInv(S)[x] <==> S[v4.result__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_result__EXPR(S) } S[x] ==> v4._S_result__EXPR(S)[v4.result__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_result__EXPRInv(S) } S[x] ==> v4._S_result__EXPRInv(S)[v4.result__EXPRInv(x)]);

axiom (forall x: int :: { v4.result__EXPR(x) } v4.result__EXPR(x) == v4.INT_ADD(x, 12));

axiom (forall x: int :: { v4.result__EXPRInv(x) } v4.result__EXPRInv(x) == v4.INT_SUB(x, 12));

axiom (forall x: int :: { v4.result__EXPR(x) } v4.result__EXPR(x) == v4.PLUS(x, 1, 12));

axiom (forall x: int, y: int :: { v4.INT_EQ(x, y): bool } v4.INT_EQ(x, y): bool <==> x == y);

axiom (forall x: int, y: int :: { v4.INT_NEQ(x, y): bool } v4.INT_NEQ(x, y): bool <==> x != y);

axiom (forall x: int, y: int :: { v4.INT_ADD(x, y): int } v4.INT_ADD(x, y): int == x + y);

axiom (forall x: int, y: int :: { v4.INT_SUB(x, y): int } v4.INT_SUB(x, y): int == x - y);

axiom (forall x: int, y: int :: { v4.INT_MULT(x, y): int } v4.INT_MULT(x, y): int == x * y);

axiom (forall x: int, y: int :: { v4.INT_DIV(x, y): int } v4.INT_DIV(x, y): int == x div y);

axiom (forall x: int, y: int :: { v4.INT_LT(x, y): bool } v4.INT_LT(x, y): bool <==> x < y);

axiom (forall x: int, y: int :: { v4.INT_ULT(x, y): bool } v4.INT_ULT(x, y): bool <==> x < y);

axiom (forall x: int, y: int :: { v4.INT_LEQ(x, y): bool } v4.INT_LEQ(x, y): bool <==> x <= y);

axiom (forall x: int, y: int :: { v4.INT_ULEQ(x, y): bool } v4.INT_ULEQ(x, y): bool <==> x <= y);

axiom (forall x: int, y: int :: { v4.INT_GT(x, y): bool } v4.INT_GT(x, y): bool <==> x > y);

axiom (forall x: int, y: int :: { v4.INT_UGT(x, y): bool } v4.INT_UGT(x, y): bool <==> x > y);

axiom (forall x: int, y: int :: { v4.INT_GEQ(x, y): bool } v4.INT_GEQ(x, y): bool <==> x >= y);

axiom (forall x: int, y: int :: { v4.INT_UGEQ(x, y): bool } v4.INT_UGEQ(x, y): bool <==> x >= y);

axiom (forall x: bv32, y: bv32 :: { v4.BV32_EQ(x, y): bool } v4.BV32_EQ(x, y): bool <==> x == y);

axiom (forall x: bv32, y: bv32 :: { v4.BV32_NEQ(x, y): bool } v4.BV32_NEQ(x, y): bool <==> x != y);

axiom (forall a: int, b: int, size: int :: { v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size) } v4.INT_LEQ(v4.INT_MULT(size, v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size)), v4.INT_SUB(a, b)) && v4.INT_LT(v4.INT_SUB(a, b), v4.INT_MULT(size, v4.INT_ADD(v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size), 1))));

axiom (forall a: int, b: int, size: int :: { v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size) } v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, 1) == v4.INT_SUB(a, b));

axiom (forall a: int, a_size: int, b: int :: { v4.MINUS_LEFT_PTR(a, a_size, b) } v4.MINUS_LEFT_PTR(a, a_size, b) == v4.INT_SUB(a, v4.INT_MULT(a_size, b)));

axiom (forall a: int, a_size: int, b: int :: { v4.PLUS(a, a_size, b) } v4.PLUS(a, a_size, b) == v4.INT_ADD(a, v4.INT_MULT(a_size, b)));

axiom (forall a: int, b: int :: { v4.MULT(a, b) } v4.MULT(a, b) == v4.INT_MULT(a, b));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a >= 0 && b > 0 ==> b * v4.DIV(a, b) <= a && a < b * (v4.DIV(a, b) + 1));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a >= 0 && b < 0 ==> b * v4.DIV(a, b) <= a && a < b * (v4.DIV(a, b) - 1));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a < 0 && b > 0 ==> b * v4.DIV(a, b) >= a && a > b * (v4.DIV(a, b) - 1));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a < 0 && b < 0 ==> b * v4.DIV(a, b) >= a && a > b * (v4.DIV(a, b) + 1));

axiom v4.POW2(1);

axiom v4.POW2(2);

axiom v4.POW2(4);

axiom v4.POW2(8);

axiom v4.POW2(16);

axiom v4.POW2(32);

axiom v4.POW2(64);

axiom v4.POW2(128);

axiom v4.POW2(256);

axiom v4.POW2(512);

axiom v4.POW2(1024);

axiom v4.POW2(2048);

axiom v4.POW2(4096);

axiom v4.POW2(8192);

axiom v4.POW2(16384);

axiom v4.POW2(32768);

axiom v4.POW2(65536);

axiom v4.POW2(131072);

axiom v4.POW2(262144);

axiom v4.POW2(524288);

axiom v4.POW2(1048576);

axiom v4.POW2(2097152);

axiom v4.POW2(4194304);

axiom v4.POW2(8388608);

axiom v4.POW2(16777216);

axiom v4.POW2(33554432);

axiom (forall a: int, b: int :: { v4.BIT_BAND(a, b) } a == b ==> v4.BIT_BAND(a, b) == a);

axiom (forall a: int, b: int :: { v4.BIT_BAND(a, b) } v4.POW2(a) && v4.POW2(b) && a != b ==> v4.BIT_BAND(a, b) == 0);

axiom (forall a: int, b: int :: { v4.BIT_BAND(a, b) } a == 0 || b == 0 ==> v4.BIT_BAND(a, b) == 0);

axiom (forall a: bool, b: int, c: int :: { v4.choose(a, b, c) } a ==> v4.choose(a, b, c) == b);

axiom (forall a: bool, b: int, c: int :: { v4.choose(a, b, c) } !a ==> v4.choose(a, b, c) == c);

axiom (forall a: bool :: { v4.LIFT(a) } a <==> v4.LIFT(a) != 0);

axiom (forall a: int :: { v4.PTR_NOT(a) } a == 0 ==> v4.PTR_NOT(a) != 0);

axiom (forall a: int :: { v4.PTR_NOT(a) } a != 0 ==> v4.PTR_NOT(a) == 0);

axiom (forall a: int :: { v4.NULL_CHECK(a) } a == 0 ==> v4.NULL_CHECK(a) != 0);

axiom (forall a: int :: { v4.NULL_CHECK(a) } a != 0 ==> v4.NULL_CHECK(a) == 0);

axiom (forall n: int, x: int, y: int :: { v4.AtLeast(n, x)[y] } v4.AtLeast(n, x)[y] ==> v4.INT_LEQ(x, y) && v4.Rep(n, x) == v4.Rep(n, y));

axiom (forall n: int, x: int, y: int :: { v4.AtLeast(n, x), v4.Rep(n, x), v4.Rep(n, y) } v4.INT_LEQ(x, y) && v4.Rep(n, x) == v4.Rep(n, y) ==> v4.AtLeast(n, x)[y]);

axiom (forall n: int, x: int :: { v4.AtLeast(n, x) } v4.AtLeast(n, x)[x]);

axiom (forall n: int, x: int, z: int :: { v4.PLUS(x, n, z) } v4.Rep(n, x) == v4.Rep(n, v4.PLUS(x, n, z)));

axiom (forall n: int, x: int :: { v4.Rep(n, x) } (exists k: int :: v4.INT_SUB(v4.Rep(n, x), x) == v4.INT_MULT(n, k)));

axiom (forall x: int, n: int, z: int :: { v4.Array(x, n, z) } v4.INT_LEQ(z, 0) ==> v4.Equal(v4.Array(x, n, z), v4.Empty()));

axiom (forall x: int, n: int, z: int :: { v4.Array(x, n, z) } v4.INT_GT(z, 0) ==> v4.Equal(v4.Array(x, n, z), v4.Difference(v4.AtLeast(n, x), v4.AtLeast(n, v4.PLUS(x, n, z)))));

axiom (forall x: int :: !v4.Empty()[x]);

axiom (forall x: int :: v4.SetTrue()[x]);

axiom (forall x: int, y: int :: { v4.Singleton(y)[x] } v4.Singleton(y)[x] <==> x == y);

axiom (forall y: int :: { v4.Singleton(y) } v4.Singleton(y)[y]);

axiom (forall x: int, S: [int]bool, T: [int]bool :: { v4.Union(S, T)[x] } { v4.Union(S, T), S[x] } { v4.Union(S, T), T[x] } v4.Union(S, T)[x] <==> S[x] || T[x]);

axiom (forall x: int, S: [int]bool, T: [int]bool :: { v4.Intersection(S, T)[x] } { v4.Intersection(S, T), S[x] } { v4.Intersection(S, T), T[x] } v4.Intersection(S, T)[x] <==> S[x] && T[x]);

axiom (forall x: int, S: [int]bool, T: [int]bool :: { v4.Difference(S, T)[x] } { v4.Difference(S, T), S[x] } { v4.Difference(S, T), T[x] } v4.Difference(S, T)[x] <==> S[x] && !T[x]);

axiom (forall S: [int]bool, T: [int]bool :: { v4.Equal(S, T) } v4.Equal(S, T) <==> v4.Subset(S, T) && v4.Subset(T, S));

axiom (forall x: int, S: [int]bool, T: [int]bool :: { S[x], v4.Subset(S, T) } { T[x], v4.Subset(S, T) } S[x] && v4.Subset(S, T) ==> T[x]);

axiom (forall S: [int]bool, T: [int]bool :: { v4.Subset(S, T) } v4.Subset(S, T) || (exists x: int :: S[x] && !T[x]));

axiom (forall x: int, S: [int]bool, T: [int]bool :: { S[x], v4.Disjoint(S, T) } { T[x], v4.Disjoint(S, T) } !(S[x] && v4.Disjoint(S, T) && T[x]));

axiom (forall S: [int]bool, T: [int]bool :: { v4.Disjoint(S, T) } v4.Disjoint(S, T) || (exists x: int :: S[x] && T[x]));

axiom (forall f: [int]int, x: int :: { v4.Inverse(f, f[x]) } v4.Inverse(f, f[x])[x]);

axiom (forall f: [int]int, x: int, y: int :: { v4.Inverse(f, y), f[x] } v4.Inverse(f, y)[x] ==> f[x] == y);

axiom (forall f: [int]int, x: int, y: int :: { v4.Inverse(f[x := y], y) } v4.Equal(v4.Inverse(f[x := y], y), v4.Union(v4.Inverse(f, y), v4.Singleton(x))));

axiom (forall f: [int]int, x: int, y: int, z: int :: { v4.Inverse(f[x := y], z) } y == z || v4.Equal(v4.Inverse(f[x := y], z), v4.Difference(v4.Inverse(f, z), v4.Singleton(x))));

axiom (forall x: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M)[x] } v4.Dereference(S, M)[x] ==> (exists y: int :: x == M[y] && S[y]));

axiom (forall x: int, S: [int]bool, M: [int]int :: { M[x], S[x], v4.Dereference(S, M) } S[x] ==> v4.Dereference(S, M)[M[x]]);

axiom (forall x: int, y: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M[x := y]) } !S[x] ==> v4.Equal(v4.Dereference(S, M[x := y]), v4.Dereference(S, M)));

axiom (forall x: int, y: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M[x := y]) } S[x] && v4.Equal(v4.Intersection(v4.Inverse(M, M[x]), S), v4.Singleton(x)) ==> v4.Equal(v4.Dereference(S, M[x := y]), v4.Union(v4.Difference(v4.Dereference(S, M), v4.Singleton(M[x])), v4.Singleton(y))));

axiom (forall x: int, y: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M[x := y]) } S[x] && !v4.Equal(v4.Intersection(v4.Inverse(M, M[x]), S), v4.Singleton(x)) ==> v4.Equal(v4.Dereference(S, M[x := y]), v4.Union(v4.Dereference(S, M), v4.Singleton(y))));

axiom (forall M: [name][int]int, x: int :: { v4.Unified(M)[x] } v4.Unified(M)[x] == M[v4.Field(x)][x]);

axiom (forall M: [name][int]int, x: int, y: int :: { v4.Unified(M[v4.Field(x) := M[v4.Field(x)][x := y]]) } v4.Unified(M[v4.Field(x) := M[v4.Field(x)][x := y]]) == v4.Unified(M)[x := y]);

procedure v4.havoc_assert(i: int);



procedure v4.havoc_assume(i: int);



procedure v4.__HAVOC_free(a: int);



procedure v4.__HAVOC_malloc(obj_size: int) returns (new: int);
  free ensures new == _uf_v4.__HAVOC_malloc_new(obj_size);



procedure v4.__HAVOC_det_malloc(obj_size: int) returns (new: int);
  free ensures new == _uf_v4.__HAVOC_det_malloc_new(obj_size);



procedure v4.__HAVOC_memset_split_1(A: [int]int, p: int, c: int, n: int) returns (ret: [int]int);
  free ensures ret == _uf_v4.__HAVOC_memset_split_1_ret(A, p, c, n);



procedure v4.__HAVOC_memset_split_2(A: [int]int, p: int, c: int, n: int) returns (ret: [int]int);
  free ensures ret == _uf_v4.__HAVOC_memset_split_2_ret(A, p, c, n);



procedure v4.__HAVOC_memset_split_4(A: [int]int, p: int, c: int, n: int) returns (ret: [int]int);
  free ensures ret == _uf_v4.__HAVOC_memset_split_4_ret(A, p, c, n);



procedure v4.nondet_choice() returns (x: int);
  free ensures x == _uf_v4.nondet_choice_x();



procedure v4.det_choice() returns (x: int);
  free ensures x == _uf_v4.det_choice_x();



procedure v4._strdup(str: int) returns (new: int);
  free ensures new == _uf_v4._strdup_new(str);



procedure v4._xstrcasecmp(a0: int, a1: int) returns (ret: int);
  free ensures ret == _uf_v4._xstrcasecmp_ret(a0, a1);



procedure v4._xstrcmp(a0: int, a1: int) returns (ret: int);
  free ensures ret == _uf_v4._xstrcmp_ret(a0, a1);



procedure v4.UnsignedAdd(a0: int, a1: int) returns (ret: int);



procedure v4.UnsignedSub(a0: int, a1: int) returns (ret: int);



procedure {:inline 1} v4.Eval(e_.1: int);
  modifies v4.Mem_T.result__EXPR;
  free ensures v4.Mem_T.result__EXPR == _uf_v4.Eval_v4.Mem_T.result__EXPR(e_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.isUnsigned));



procedure v4.EvalEntry1(e_.1: int, outval_.1: int);
  modifies v4.isUnsigned, v4.Mem_T.result__EXPR, v4.Mem_T.INT4;
  free ensures v4.isUnsigned == _uf_v4.EvalEntry1_v4.isUnsigned(e_.1, outval_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.Mem_T.INT4), old(v4.isUnsigned));
  free ensures v4.Mem_T.result__EXPR == _uf_v4.EvalEntry1_v4.Mem_T.result__EXPR(e_.1, outval_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.Mem_T.INT4), old(v4.isUnsigned));
  free ensures v4.Mem_T.INT4 == _uf_v4.EvalEntry1_v4.Mem_T.INT4(e_.1, outval_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.Mem_T.INT4), old(v4.isUnsigned));



procedure v4.EvalEntry2(e_.1: int);
  modifies v4.isUnsigned, v4.Mem_T.result__EXPR;
  free ensures v4.isUnsigned == _uf_v4.EvalEntry2_v4.isUnsigned(e_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.isUnsigned));
  free ensures v4.Mem_T.result__EXPR == _uf_v4.EvalEntry2_v4.Mem_T.result__EXPR(e_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.isUnsigned));



procedure v4.__havoc_heapglobal_init();



implementation {:inline 1} v4.Eval(e_.1: int)
{
  var havoc_stringTemp: int;
  var condVal: int;
  var a1: int;
  var a2: int;
  var e: int;
  var op: int;
  var res: int;
  var result.UnsignedAdd$1: int;
  var result.UnsignedSub$2: int;
  var tempBoogie0: int;
  var tempBoogie1: int;
  var tempBoogie2: int;
  var tempBoogie3: int;
  var tempBoogie4: int;
  var tempBoogie5: int;
  var tempBoogie6: int;
  var tempBoogie7: int;
  var tempBoogie8: int;
  var tempBoogie9: int;
  var tempBoogie10: int;
  var tempBoogie11: int;
  var tempBoogie12: int;
  var tempBoogie13: int;
  var tempBoogie14: int;
  var tempBoogie15: int;
  var tempBoogie16: int;
  var tempBoogie17: int;
  var tempBoogie18: int;
  var tempBoogie19: int;
  var __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume v4.INT_LT(e_.1, v4.alloc);
    a1 := 0;
    a2 := 0;
    e := 0;
    op := 0;
    res := 0;
    result.UnsignedAdd$1 := 0;
    result.UnsignedSub$2 := 0;
    e := e_.1;
    goto label_3#2;

  label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto label_4#2;

  label_4#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto label_5#2;

  label_5#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto label_6#2;

  label_6#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto label_7#2;

  label_7#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 21} true;
    assert true;
    op := v4.Mem_T.oper__EXPR[v4.oper__EXPR(e)];
    assume v4.value_is(v4.__ctobpl_const_1, op);
    assume v4.value_is(v4.__ctobpl_const_2, e);
    assume v4.value_is(v4.__ctobpl_const_3, v4.Mem_T.oper__EXPR[v4.oper__EXPR(e)]);
    goto label_8#2;

  label_8#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 22} true;
    assert true;
    a1 := v4.Mem_T.op1__EXPR[v4.op1__EXPR(e)];
    assume v4.value_is(v4.__ctobpl_const_4, a1);
    assume v4.value_is(v4.__ctobpl_const_5, e);
    assume v4.value_is(v4.__ctobpl_const_6, v4.Mem_T.op1__EXPR[v4.op1__EXPR(e)]);
    goto label_9#2;

  label_9#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 23} true;
    assert true;
    a2 := v4.Mem_T.op2__EXPR[v4.op2__EXPR(e)];
    assume v4.value_is(v4.__ctobpl_const_7, a2);
    assume v4.value_is(v4.__ctobpl_const_8, e);
    assume v4.value_is(v4.__ctobpl_const_9, v4.Mem_T.op2__EXPR[v4.op2__EXPR(e)]);
    goto label_10#2;

  label_10#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 24} true;
    res := 0 - 1;
    assume v4.value_is(v4.__ctobpl_const_10, res);
    goto label_11#2;

  label_11#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 26} true;
    goto label_11_case_0#2, label_11_case_1#2, label_11_case_2#2;

  label_11_case_2#2:
    assume v4.INT_EQ(op, 2);
    assume v4.value_is(v4.__ctobpl_const_11, op);
    goto label_14#2;

  label_14#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 35} true;
    goto label_14_true#2, label_14_false#2;

  label_14_false#2:
    assume v4.isUnsigned == 0;
    assume v4.value_is(v4.__ctobpl_const_16, v4.isUnsigned);
    goto label_15#2;

  label_15#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 38} true;
    res := v4.MINUS_BOTH_PTR_OR_BOTH_INT(a1, a2, 1);
    assume v4.value_is(v4.__ctobpl_const_17, res);
    assume v4.value_is(v4.__ctobpl_const_18, a1);
    assume v4.value_is(v4.__ctobpl_const_19, a2);
    goto label_12#2;

  label_14_true#2:
    assume v4.isUnsigned != 0;
    assume v4.value_is(v4.__ctobpl_const_16, v4.isUnsigned);
    goto label_16#2;

  label_16#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 36} true;
    call result.UnsignedSub$2 := v4.UnsignedSub(a1, a2);
    assume v4.value_is(v4.__ctobpl_const_20, a1);
    assume v4.value_is(v4.__ctobpl_const_21, a2);
    assume v4.value_is(v4.__ctobpl_const_22, a1);
    assume v4.value_is(v4.__ctobpl_const_23, a2);
    goto label_19#2;

  label_19#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 36} true;
    res := result.UnsignedSub$2;
    assume v4.value_is(v4.__ctobpl_const_24, res);
    assume v4.value_is(v4.__ctobpl_const_25, result.UnsignedSub$2);
    goto label_12#2;

  label_11_case_1#2:
    assume v4.INT_EQ(op, 1);
    assume v4.value_is(v4.__ctobpl_const_11, op);
    goto label_13#2;

  label_13#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 29} true;
    goto label_13_true#2, label_13_false#2;

  label_13_false#2:
    assume v4.isUnsigned == 0;
    assume v4.value_is(v4.__ctobpl_const_15, v4.isUnsigned);
    goto label_20#2;

  label_20#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 32} true;
    res := v4.PLUS(a1, 1, a2);
    assume v4.value_is(v4.__ctobpl_const_26, res);
    assume v4.value_is(v4.__ctobpl_const_27, a1);
    assume v4.value_is(v4.__ctobpl_const_28, a2);
    goto label_12#2;

  label_13_true#2:
    assume v4.isUnsigned != 0;
    assume v4.value_is(v4.__ctobpl_const_15, v4.isUnsigned);
    goto label_21#2;

  label_21#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 30} true;
    call result.UnsignedAdd$1 := v4.UnsignedAdd(a1, a2);
    assume v4.value_is(v4.__ctobpl_const_29, a1);
    assume v4.value_is(v4.__ctobpl_const_30, a2);
    assume v4.value_is(v4.__ctobpl_const_31, a1);
    assume v4.value_is(v4.__ctobpl_const_32, a2);
    goto label_24#2;

  label_24#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 30} true;
    res := result.UnsignedAdd$1;
    assume v4.value_is(v4.__ctobpl_const_33, res);
    assume v4.value_is(v4.__ctobpl_const_34, result.UnsignedAdd$1);
    goto label_12#2;

  label_11_case_0#2:
    assume v4.INT_NEQ(op, 1);
    assume v4.INT_NEQ(op, 2);
    assume v4.value_is(v4.__ctobpl_const_11, op);
    goto label_12#2;

  label_12#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 41} true;
    assert true;
    v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR[v4.result__EXPR(e) := res];
    assume v4.value_is(v4.__ctobpl_const_12, e);
    assume v4.value_is(v4.__ctobpl_const_13, v4.Mem_T.result__EXPR[v4.result__EXPR(e)]);
    assume v4.value_is(v4.__ctobpl_const_14, res);
    goto label_1#2;

  label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 42} true;
    return;
}



implementation v4.EvalEntry1(e_.1: int, outval_.1: int)
{
  var havoc_stringTemp: int;
  var condVal: int;
  var e: int;
  var outval: int;
  var tempBoogie0: int;
  var tempBoogie1: int;
  var tempBoogie2: int;
  var tempBoogie3: int;
  var tempBoogie4: int;
  var tempBoogie5: int;
  var tempBoogie6: int;
  var tempBoogie7: int;
  var tempBoogie8: int;
  var tempBoogie9: int;
  var tempBoogie10: int;
  var tempBoogie11: int;
  var tempBoogie12: int;
  var tempBoogie13: int;
  var tempBoogie14: int;
  var tempBoogie15: int;
  var tempBoogie16: int;
  var tempBoogie17: int;
  var tempBoogie18: int;
  var tempBoogie19: int;
  var __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume v4.INT_LT(e_.1, v4.alloc);
    assume v4.INT_LT(outval_.1, v4.alloc);
    e := 0;
    outval := 0;
    e := e_.1;
    outval := outval_.1;
    goto label_3#2;

  label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 47} true;
    v4.isUnsigned := 1;
    assume v4.value_is(v4.__ctobpl_const_35, v4.isUnsigned);
    goto label_4#2;

  label_4#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 48} true;
    call v4.Eval(e);
    assume v4.value_is(v4.__ctobpl_const_36, e);
    assume v4.value_is(v4.__ctobpl_const_37, e);
    goto label_7#2;

  label_7#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 49} true;
    assert true;
    assert true;
    v4.Mem_T.INT4 := v4.Mem_T.INT4[outval := v4.Mem_T.result__EXPR[v4.result__EXPR(e)]];
    assume v4.value_is(v4.__ctobpl_const_38, outval);
    assume v4.value_is(v4.__ctobpl_const_39, v4.Mem_T.INT4[outval]);
    assume v4.value_is(v4.__ctobpl_const_40, e);
    assume v4.value_is(v4.__ctobpl_const_41, v4.Mem_T.result__EXPR[v4.result__EXPR(e)]);
    goto label_1#2;

  label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 50} true;
    return;
}



implementation v4.EvalEntry2(e_.1: int)
{
  var havoc_stringTemp: int;
  var condVal: int;
  var e: int;
  var tempBoogie0: int;
  var tempBoogie1: int;
  var tempBoogie2: int;
  var tempBoogie3: int;
  var tempBoogie4: int;
  var tempBoogie5: int;
  var tempBoogie6: int;
  var tempBoogie7: int;
  var tempBoogie8: int;
  var tempBoogie9: int;
  var tempBoogie10: int;
  var tempBoogie11: int;
  var tempBoogie12: int;
  var tempBoogie13: int;
  var tempBoogie14: int;
  var tempBoogie15: int;
  var tempBoogie16: int;
  var tempBoogie17: int;
  var tempBoogie18: int;
  var tempBoogie19: int;
  var __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume v4.INT_LT(e_.1, v4.alloc);
    e := 0;
    e := e_.1;
    goto label_3#2;

  label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 54} true;
    v4.isUnsigned := 0;
    assume v4.value_is(v4.__ctobpl_const_42, v4.isUnsigned);
    goto label_4#2;

  label_4#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 55} true;
    call v4.Eval(e);
    assume v4.value_is(v4.__ctobpl_const_43, e);
    assume v4.value_is(v4.__ctobpl_const_44, e);
    goto label_1#2;

  label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 56} true;
    return;
}



implementation v4.__havoc_heapglobal_init()
{

  anon0#2:
    return;
}



var v2.Mem: [name][int]int;

var v2.alloc: int;

var v2.Mem_T.INT4: [int]int;

var v2.Mem_T.op1__EXPR: [int]int;

var v2.Mem_T.op2__EXPR: [int]int;

var v2.Mem_T.oper__EXPR: [int]int;

var v2.Mem_T.result__EXPR: [int]int;

var v2.detChoiceCnt: int;

var v2.Res_KERNEL_SOURCE: [int]int;

var v2.Res_PROBED: [int]int;

const unique v2.T.oper__EXPR: name;

const unique v2.T.op1__EXPR: name;

const unique v2.T.op2__EXPR: name;

const unique v2.T.result__EXPR: name;

const unique v2.T.INT4: name;

const unique v2.T.PINT4: name;

const unique v2.T.PPINT4: name;

const unique v2.T.PP_EXPR: name;

const unique v2.T.P_EXPR: name;

const unique v2.T._EXPR: name;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 21} unique v2.__ctobpl_const_7: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 21} unique v2.__ctobpl_const_8: int;

const {:model_const "e->oper"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 19} unique v2.__ctobpl_const_3: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 20} unique v2.__ctobpl_const_4: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 20} unique v2.__ctobpl_const_5: int;

const {:model_const "e->op1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 20} unique v2.__ctobpl_const_6: int;

const {:model_const "e->op2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 21} unique v2.__ctobpl_const_9: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 22} unique v2.__ctobpl_const_10: int;

const {:model_const "op"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 24} unique v2.__ctobpl_const_11: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 35} unique v2.__ctobpl_const_12: int;

const {:model_const "e->result"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 35} unique v2.__ctobpl_const_13: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 35} unique v2.__ctobpl_const_14: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 27} unique v2.__ctobpl_const_15: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 27} unique v2.__ctobpl_const_16: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 27} unique v2.__ctobpl_const_17: int;

const {:model_const "res"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 29} unique v2.__ctobpl_const_18: int;

const {:model_const "a1"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 29} unique v2.__ctobpl_const_19: int;

const {:model_const "a2"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 29} unique v2.__ctobpl_const_20: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 40} unique v2.__ctobpl_const_21: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 40} unique v2.__ctobpl_const_22: int;

const {:model_const "outval"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 41} unique v2.__ctobpl_const_23: int;

const {:model_const "*outval"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 41} unique v2.__ctobpl_const_24: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 41} unique v2.__ctobpl_const_25: int;

const {:model_const "e->result"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 41} unique v2.__ctobpl_const_26: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 46} unique v2.__ctobpl_const_27: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 46} unique v2.__ctobpl_const_28: int;

const {:model_const "op"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 19} unique v2.__ctobpl_const_1: int;

const {:model_const "e"} {:sourceFile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceLine 19} unique v2.__ctobpl_const_2: int;

axiom (forall b0: byte, c0: byte :: { v4.OneByteToInt(b0), v4.OneByteToInt(c0) } v4.OneByteToInt(b0) == v4.OneByteToInt(c0) ==> b0 == c0);

axiom (forall b0: byte, b1: byte, c0: byte, c1: byte :: { v4.TwoBytesToInt(b0, b1), v4.TwoBytesToInt(c0, c1) } v4.TwoBytesToInt(b0, b1) == v4.TwoBytesToInt(c0, c1) ==> b0 == c0 && b1 == c1);

axiom (forall b0: byte, b1: byte, b2: byte, b3: byte, c0: byte, c1: byte, c2: byte, c3: byte :: { v4.FourBytesToInt(b0, b1, b2, b3), v4.FourBytesToInt(c0, c1, c2, c3) } v4.FourBytesToInt(b0, b1, b2, b3) == v4.FourBytesToInt(c0, c1, c2, c3) ==> b0 == c0 && b1 == c1 && b2 == c2 && b3 == c3);

axiom (forall x: int :: { v4.Base(x) } v4.INT_LEQ(v4.Base(x), x));

axiom (forall a: int, t: name :: { v4.Match(a, v4.T.Ptr(t)) } v4.Match(a, v4.T.Ptr(t)) <==> v4.Field(a) == v4.T.Ptr(t));

axiom (forall b: int, a: int, t: name :: { v4.MatchBase(b, a, v4.T.Ptr(t)) } v4.MatchBase(b, a, v4.T.Ptr(t)) <==> v4.Base(a) == b);

axiom (forall v: int, t: name :: { v4.HasType(v, v4.T.Ptr(t)) } v4.HasType(v, v4.T.Ptr(t)) <==> v == 0 || (v4.INT_GT(v, 0) && v4.Match(v, t) && v4.MatchBase(v4.Base(v), v, t)));

axiom (forall x: int, S: [int]bool :: { v4._S_op1__EXPR(S)[x] } v4._S_op1__EXPR(S)[x] <==> S[v4.op1__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_op1__EXPRInv(S)[x] } v4._S_op1__EXPRInv(S)[x] <==> S[v4.op1__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op1__EXPR(S) } S[x] ==> v4._S_op1__EXPR(S)[v4.op1__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op1__EXPRInv(S) } S[x] ==> v4._S_op1__EXPRInv(S)[v4.op1__EXPRInv(x)]);

axiom (forall x: int :: { v4.op1__EXPR(x) } v4.op1__EXPR(x) == v4.INT_ADD(x, 4));

axiom (forall x: int :: { v4.op1__EXPRInv(x) } v4.op1__EXPRInv(x) == v4.INT_SUB(x, 4));

axiom (forall x: int :: { v4.op1__EXPR(x) } v4.op1__EXPR(x) == v4.PLUS(x, 1, 4));

axiom (forall x: int, S: [int]bool :: { v4._S_op2__EXPR(S)[x] } v4._S_op2__EXPR(S)[x] <==> S[v4.op2__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_op2__EXPRInv(S)[x] } v4._S_op2__EXPRInv(S)[x] <==> S[v4.op2__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op2__EXPR(S) } S[x] ==> v4._S_op2__EXPR(S)[v4.op2__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_op2__EXPRInv(S) } S[x] ==> v4._S_op2__EXPRInv(S)[v4.op2__EXPRInv(x)]);

axiom (forall x: int :: { v4.op2__EXPR(x) } v4.op2__EXPR(x) == v4.INT_ADD(x, 8));

axiom (forall x: int :: { v4.op2__EXPRInv(x) } v4.op2__EXPRInv(x) == v4.INT_SUB(x, 8));

axiom (forall x: int :: { v4.op2__EXPR(x) } v4.op2__EXPR(x) == v4.PLUS(x, 1, 8));

axiom (forall x: int, S: [int]bool :: { v4._S_oper__EXPR(S)[x] } v4._S_oper__EXPR(S)[x] <==> S[v4.oper__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_oper__EXPRInv(S)[x] } v4._S_oper__EXPRInv(S)[x] <==> S[v4.oper__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_oper__EXPR(S) } S[x] ==> v4._S_oper__EXPR(S)[v4.oper__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_oper__EXPRInv(S) } S[x] ==> v4._S_oper__EXPRInv(S)[v4.oper__EXPRInv(x)]);

axiom (forall x: int :: { v4.oper__EXPR(x) } v4.oper__EXPR(x) == v4.INT_ADD(x, 0));

axiom (forall x: int :: { v4.oper__EXPRInv(x) } v4.oper__EXPRInv(x) == v4.INT_SUB(x, 0));

axiom (forall x: int :: { v4.oper__EXPR(x) } v4.oper__EXPR(x) == v4.PLUS(x, 1, 0));

axiom (forall x: int, S: [int]bool :: { v4._S_result__EXPR(S)[x] } v4._S_result__EXPR(S)[x] <==> S[v4.result__EXPRInv(x)]);

axiom (forall x: int, S: [int]bool :: { v4._S_result__EXPRInv(S)[x] } v4._S_result__EXPRInv(S)[x] <==> S[v4.result__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_result__EXPR(S) } S[x] ==> v4._S_result__EXPR(S)[v4.result__EXPR(x)]);

axiom (forall x: int, S: [int]bool :: { S[x], v4._S_result__EXPRInv(S) } S[x] ==> v4._S_result__EXPRInv(S)[v4.result__EXPRInv(x)]);

axiom (forall x: int :: { v4.result__EXPR(x) } v4.result__EXPR(x) == v4.INT_ADD(x, 12));

axiom (forall x: int :: { v4.result__EXPRInv(x) } v4.result__EXPRInv(x) == v4.INT_SUB(x, 12));

axiom (forall x: int :: { v4.result__EXPR(x) } v4.result__EXPR(x) == v4.PLUS(x, 1, 12));

axiom (forall x: int, y: int :: { v4.INT_EQ(x, y): bool } v4.INT_EQ(x, y): bool <==> x == y);

axiom (forall x: int, y: int :: { v4.INT_NEQ(x, y): bool } v4.INT_NEQ(x, y): bool <==> x != y);

axiom (forall x: int, y: int :: { v4.INT_ADD(x, y): int } v4.INT_ADD(x, y): int == x + y);

axiom (forall x: int, y: int :: { v4.INT_SUB(x, y): int } v4.INT_SUB(x, y): int == x - y);

axiom (forall x: int, y: int :: { v4.INT_MULT(x, y): int } v4.INT_MULT(x, y): int == x * y);

axiom (forall x: int, y: int :: { v4.INT_DIV(x, y): int } v4.INT_DIV(x, y): int == x div y);

axiom (forall x: int, y: int :: { v4.INT_LT(x, y): bool } v4.INT_LT(x, y): bool <==> x < y);

axiom (forall x: int, y: int :: { v4.INT_ULT(x, y): bool } v4.INT_ULT(x, y): bool <==> x < y);

axiom (forall x: int, y: int :: { v4.INT_LEQ(x, y): bool } v4.INT_LEQ(x, y): bool <==> x <= y);

axiom (forall x: int, y: int :: { v4.INT_ULEQ(x, y): bool } v4.INT_ULEQ(x, y): bool <==> x <= y);

axiom (forall x: int, y: int :: { v4.INT_GT(x, y): bool } v4.INT_GT(x, y): bool <==> x > y);

axiom (forall x: int, y: int :: { v4.INT_UGT(x, y): bool } v4.INT_UGT(x, y): bool <==> x > y);

axiom (forall x: int, y: int :: { v4.INT_GEQ(x, y): bool } v4.INT_GEQ(x, y): bool <==> x >= y);

axiom (forall x: int, y: int :: { v4.INT_UGEQ(x, y): bool } v4.INT_UGEQ(x, y): bool <==> x >= y);

axiom (forall x: bv32, y: bv32 :: { v4.BV32_EQ(x, y): bool } v4.BV32_EQ(x, y): bool <==> x == y);

axiom (forall x: bv32, y: bv32 :: { v4.BV32_NEQ(x, y): bool } v4.BV32_NEQ(x, y): bool <==> x != y);

axiom (forall a: int, b: int, size: int :: { v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size) } v4.INT_LEQ(v4.INT_MULT(size, v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size)), v4.INT_SUB(a, b)) && v4.INT_LT(v4.INT_SUB(a, b), v4.INT_MULT(size, v4.INT_ADD(v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size), 1))));

axiom (forall a: int, b: int, size: int :: { v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, size) } v4.MINUS_BOTH_PTR_OR_BOTH_INT(a, b, 1) == v4.INT_SUB(a, b));

axiom (forall a: int, a_size: int, b: int :: { v4.MINUS_LEFT_PTR(a, a_size, b) } v4.MINUS_LEFT_PTR(a, a_size, b) == v4.INT_SUB(a, v4.INT_MULT(a_size, b)));

axiom (forall a: int, a_size: int, b: int :: { v4.PLUS(a, a_size, b) } v4.PLUS(a, a_size, b) == v4.INT_ADD(a, v4.INT_MULT(a_size, b)));

axiom (forall a: int, b: int :: { v4.MULT(a, b) } v4.MULT(a, b) == v4.INT_MULT(a, b));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a >= 0 && b > 0 ==> b * v4.DIV(a, b) <= a && a < b * (v4.DIV(a, b) + 1));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a >= 0 && b < 0 ==> b * v4.DIV(a, b) <= a && a < b * (v4.DIV(a, b) - 1));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a < 0 && b > 0 ==> b * v4.DIV(a, b) >= a && a > b * (v4.DIV(a, b) - 1));

axiom (forall a: int, b: int :: { v4.DIV(a, b) } a < 0 && b < 0 ==> b * v4.DIV(a, b) >= a && a > b * (v4.DIV(a, b) + 1));

axiom v4.POW2(1);

axiom v4.POW2(2);

axiom v4.POW2(4);

axiom v4.POW2(8);

axiom v4.POW2(16);

axiom v4.POW2(32);

axiom v4.POW2(64);

axiom v4.POW2(128);

axiom v4.POW2(256);

axiom v4.POW2(512);

axiom v4.POW2(1024);

axiom v4.POW2(2048);

axiom v4.POW2(4096);

axiom v4.POW2(8192);

axiom v4.POW2(16384);

axiom v4.POW2(32768);

axiom v4.POW2(65536);

axiom v4.POW2(131072);

axiom v4.POW2(262144);

axiom v4.POW2(524288);

axiom v4.POW2(1048576);

axiom v4.POW2(2097152);

axiom v4.POW2(4194304);

axiom v4.POW2(8388608);

axiom v4.POW2(16777216);

axiom v4.POW2(33554432);

axiom (forall a: int, b: int :: { v4.BIT_BAND(a, b) } a == b ==> v4.BIT_BAND(a, b) == a);

axiom (forall a: int, b: int :: { v4.BIT_BAND(a, b) } v4.POW2(a) && v4.POW2(b) && a != b ==> v4.BIT_BAND(a, b) == 0);

axiom (forall a: int, b: int :: { v4.BIT_BAND(a, b) } a == 0 || b == 0 ==> v4.BIT_BAND(a, b) == 0);

axiom (forall a: bool, b: int, c: int :: { v4.choose(a, b, c) } a ==> v4.choose(a, b, c) == b);

axiom (forall a: bool, b: int, c: int :: { v4.choose(a, b, c) } !a ==> v4.choose(a, b, c) == c);

axiom (forall a: bool :: { v4.LIFT(a) } a <==> v4.LIFT(a) != 0);

axiom (forall a: int :: { v4.PTR_NOT(a) } a == 0 ==> v4.PTR_NOT(a) != 0);

axiom (forall a: int :: { v4.PTR_NOT(a) } a != 0 ==> v4.PTR_NOT(a) == 0);

axiom (forall a: int :: { v4.NULL_CHECK(a) } a == 0 ==> v4.NULL_CHECK(a) != 0);

axiom (forall a: int :: { v4.NULL_CHECK(a) } a != 0 ==> v4.NULL_CHECK(a) == 0);

axiom (forall n: int, x: int, y: int :: { v4.AtLeast(n, x)[y] } v4.AtLeast(n, x)[y] ==> v4.INT_LEQ(x, y) && v4.Rep(n, x) == v4.Rep(n, y));

axiom (forall n: int, x: int, y: int :: { v4.AtLeast(n, x), v4.Rep(n, x), v4.Rep(n, y) } v4.INT_LEQ(x, y) && v4.Rep(n, x) == v4.Rep(n, y) ==> v4.AtLeast(n, x)[y]);

axiom (forall n: int, x: int :: { v4.AtLeast(n, x) } v4.AtLeast(n, x)[x]);

axiom (forall n: int, x: int, z: int :: { v4.PLUS(x, n, z) } v4.Rep(n, x) == v4.Rep(n, v4.PLUS(x, n, z)));

axiom (forall n: int, x: int :: { v4.Rep(n, x) } (exists k: int :: v4.INT_SUB(v4.Rep(n, x), x) == v4.INT_MULT(n, k)));

axiom (forall x: int, n: int, z: int :: { v4.Array(x, n, z) } v4.INT_LEQ(z, 0) ==> v4.Equal(v4.Array(x, n, z), v4.Empty()));

axiom (forall x: int, n: int, z: int :: { v4.Array(x, n, z) } v4.INT_GT(z, 0) ==> v4.Equal(v4.Array(x, n, z), v4.Difference(v4.AtLeast(n, x), v4.AtLeast(n, v4.PLUS(x, n, z)))));

axiom (forall x: int :: !v4.Empty()[x]);

axiom (forall x: int :: v4.SetTrue()[x]);

axiom (forall x: int, y: int :: { v4.Singleton(y)[x] } v4.Singleton(y)[x] <==> x == y);

axiom (forall y: int :: { v4.Singleton(y) } v4.Singleton(y)[y]);

axiom (forall x: int, S: [int]bool, T: [int]bool :: { v4.Union(S, T)[x] } { v4.Union(S, T), S[x] } { v4.Union(S, T), T[x] } v4.Union(S, T)[x] <==> S[x] || T[x]);

axiom (forall x: int, S: [int]bool, T: [int]bool :: { v4.Intersection(S, T)[x] } { v4.Intersection(S, T), S[x] } { v4.Intersection(S, T), T[x] } v4.Intersection(S, T)[x] <==> S[x] && T[x]);

axiom (forall x: int, S: [int]bool, T: [int]bool :: { v4.Difference(S, T)[x] } { v4.Difference(S, T), S[x] } { v4.Difference(S, T), T[x] } v4.Difference(S, T)[x] <==> S[x] && !T[x]);

axiom (forall S: [int]bool, T: [int]bool :: { v4.Equal(S, T) } v4.Equal(S, T) <==> v4.Subset(S, T) && v4.Subset(T, S));

axiom (forall x: int, S: [int]bool, T: [int]bool :: { S[x], v4.Subset(S, T) } { T[x], v4.Subset(S, T) } S[x] && v4.Subset(S, T) ==> T[x]);

axiom (forall S: [int]bool, T: [int]bool :: { v4.Subset(S, T) } v4.Subset(S, T) || (exists x: int :: S[x] && !T[x]));

axiom (forall x: int, S: [int]bool, T: [int]bool :: { S[x], v4.Disjoint(S, T) } { T[x], v4.Disjoint(S, T) } !(S[x] && v4.Disjoint(S, T) && T[x]));

axiom (forall S: [int]bool, T: [int]bool :: { v4.Disjoint(S, T) } v4.Disjoint(S, T) || (exists x: int :: S[x] && T[x]));

axiom (forall f: [int]int, x: int :: { v4.Inverse(f, f[x]) } v4.Inverse(f, f[x])[x]);

axiom (forall f: [int]int, x: int, y: int :: { v4.Inverse(f, y), f[x] } v4.Inverse(f, y)[x] ==> f[x] == y);

axiom (forall f: [int]int, x: int, y: int :: { v4.Inverse(f[x := y], y) } v4.Equal(v4.Inverse(f[x := y], y), v4.Union(v4.Inverse(f, y), v4.Singleton(x))));

axiom (forall f: [int]int, x: int, y: int, z: int :: { v4.Inverse(f[x := y], z) } y == z || v4.Equal(v4.Inverse(f[x := y], z), v4.Difference(v4.Inverse(f, z), v4.Singleton(x))));

axiom (forall x: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M)[x] } v4.Dereference(S, M)[x] ==> (exists y: int :: x == M[y] && S[y]));

axiom (forall x: int, S: [int]bool, M: [int]int :: { M[x], S[x], v4.Dereference(S, M) } S[x] ==> v4.Dereference(S, M)[M[x]]);

axiom (forall x: int, y: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M[x := y]) } !S[x] ==> v4.Equal(v4.Dereference(S, M[x := y]), v4.Dereference(S, M)));

axiom (forall x: int, y: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M[x := y]) } S[x] && v4.Equal(v4.Intersection(v4.Inverse(M, M[x]), S), v4.Singleton(x)) ==> v4.Equal(v4.Dereference(S, M[x := y]), v4.Union(v4.Difference(v4.Dereference(S, M), v4.Singleton(M[x])), v4.Singleton(y))));

axiom (forall x: int, y: int, S: [int]bool, M: [int]int :: { v4.Dereference(S, M[x := y]) } S[x] && !v4.Equal(v4.Intersection(v4.Inverse(M, M[x]), S), v4.Singleton(x)) ==> v4.Equal(v4.Dereference(S, M[x := y]), v4.Union(v4.Dereference(S, M), v4.Singleton(y))));

axiom (forall M: [name][int]int, x: int :: { v4.Unified(M)[x] } v4.Unified(M)[x] == M[v4.Field(x)][x]);

axiom (forall M: [name][int]int, x: int, y: int :: { v4.Unified(M[v4.Field(x) := M[v4.Field(x)][x := y]]) } v4.Unified(M[v4.Field(x) := M[v4.Field(x)][x := y]]) == v4.Unified(M)[x := y]);

procedure v2.havoc_assert(i: int);



procedure v2.havoc_assume(i: int);



procedure v2.__HAVOC_free(a: int);



procedure v2.__HAVOC_malloc(obj_size: int) returns (new: int);
  free ensures new == _uf_v4.__HAVOC_malloc_new(obj_size);



procedure v2.__HAVOC_det_malloc(obj_size: int) returns (new: int);
  free ensures new == _uf_v4.__HAVOC_det_malloc_new(obj_size);



procedure v2.__HAVOC_memset_split_1(A: [int]int, p: int, c: int, n: int) returns (ret: [int]int);
  free ensures ret == _uf_v4.__HAVOC_memset_split_1_ret(A, p, c, n);



procedure v2.__HAVOC_memset_split_2(A: [int]int, p: int, c: int, n: int) returns (ret: [int]int);
  free ensures ret == _uf_v4.__HAVOC_memset_split_2_ret(A, p, c, n);



procedure v2.__HAVOC_memset_split_4(A: [int]int, p: int, c: int, n: int) returns (ret: [int]int);
  free ensures ret == _uf_v4.__HAVOC_memset_split_4_ret(A, p, c, n);



procedure v2.nondet_choice() returns (x: int);
  free ensures x == _uf_v4.nondet_choice_x();



procedure v2.det_choice() returns (x: int);
  free ensures x == _uf_v4.det_choice_x();



procedure v2._strdup(str: int) returns (new: int);
  free ensures new == _uf_v4._strdup_new(str);



procedure v2._xstrcasecmp(a0: int, a1: int) returns (ret: int);
  free ensures ret == _uf_v4._xstrcasecmp_ret(a0, a1);



procedure v2._xstrcmp(a0: int, a1: int) returns (ret: int);
  free ensures ret == _uf_v4._xstrcmp_ret(a0, a1);



procedure {:inline 1} v2.Eval(e_.1: int);
  modifies v4.Mem_T.result__EXPR;
  free ensures v4.Mem_T.result__EXPR == _uf_v4.Eval_v4.Mem_T.result__EXPR(e_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.isUnsigned));



procedure v2.EvalEntry1(e_.1: int, outval_.1: int);
  modifies v4.Mem_T.result__EXPR, v4.Mem_T.INT4;
  free ensures v4.Mem_T.result__EXPR == _uf_v4.EvalEntry1_v4.Mem_T.result__EXPR(e_.1, outval_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.Mem_T.INT4), old(v4.isUnsigned));
  free ensures v4.Mem_T.INT4 == _uf_v4.EvalEntry1_v4.Mem_T.INT4(e_.1, outval_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.Mem_T.INT4), old(v4.isUnsigned));



procedure v2.EvalEntry2(e_.1: int);
  modifies v4.Mem_T.result__EXPR;
  free ensures v4.Mem_T.result__EXPR == _uf_v4.EvalEntry2_v4.Mem_T.result__EXPR(e_.1, old(v4.alloc), old(v4.Mem_T.oper__EXPR), old(v4.Mem_T.op1__EXPR), old(v4.Mem_T.op2__EXPR), old(v4.Mem_T.result__EXPR), old(v4.isUnsigned));



procedure v2.__havoc_heapglobal_init();



implementation {:inline 1} v2.Eval(e_.1: int)
{
  var havoc_stringTemp: int;
  var condVal: int;
  var a1: int;
  var a2: int;
  var e: int;
  var op: int;
  var res: int;
  var tempBoogie0: int;
  var tempBoogie1: int;
  var tempBoogie2: int;
  var tempBoogie3: int;
  var tempBoogie4: int;
  var tempBoogie5: int;
  var tempBoogie6: int;
  var tempBoogie7: int;
  var tempBoogie8: int;
  var tempBoogie9: int;
  var tempBoogie10: int;
  var tempBoogie11: int;
  var tempBoogie12: int;
  var tempBoogie13: int;
  var tempBoogie14: int;
  var tempBoogie15: int;
  var tempBoogie16: int;
  var tempBoogie17: int;
  var tempBoogie18: int;
  var tempBoogie19: int;
  var __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume v4.INT_LT(e_.1, v4.alloc);
    a1 := 0;
    a2 := 0;
    e := 0;
    op := 0;
    res := 0;
    e := e_.1;
    goto label_3#2;

  label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto label_4#2;

  label_4#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto label_5#2;

  label_5#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto label_6#2;

  label_6#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto label_7#2;

  label_7#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 19} true;
    assert true;
    op := v4.Mem_T.oper__EXPR[v4.oper__EXPR(e)];
    assume v4.value_is(v2.__ctobpl_const_1, op);
    assume v4.value_is(v2.__ctobpl_const_2, e);
    assume v4.value_is(v2.__ctobpl_const_3, v4.Mem_T.oper__EXPR[v4.oper__EXPR(e)]);
    goto label_8#2;

  label_8#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 20} true;
    assert true;
    a1 := v4.Mem_T.op1__EXPR[v4.op1__EXPR(e)];
    assume v4.value_is(v2.__ctobpl_const_4, a1);
    assume v4.value_is(v2.__ctobpl_const_5, e);
    assume v4.value_is(v2.__ctobpl_const_6, v4.Mem_T.op1__EXPR[v4.op1__EXPR(e)]);
    goto label_9#2;

  label_9#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 21} true;
    assert true;
    a2 := v4.Mem_T.op2__EXPR[v4.op2__EXPR(e)];
    assume v4.value_is(v2.__ctobpl_const_7, a2);
    assume v4.value_is(v2.__ctobpl_const_8, e);
    assume v4.value_is(v2.__ctobpl_const_9, v4.Mem_T.op2__EXPR[v4.op2__EXPR(e)]);
    goto label_10#2;

  label_10#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 22} true;
    res := 0 - 1;
    assume v4.value_is(v2.__ctobpl_const_10, res);
    goto label_11#2;

  label_11#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 24} true;
    goto label_11_case_0#2, label_11_case_1#2, label_11_case_2#2;

  label_11_case_2#2:
    assume v4.INT_EQ(op, 2);
    assume v4.value_is(v2.__ctobpl_const_11, op);
    goto label_14#2;

  label_14#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 29} true;
    res := v4.MINUS_BOTH_PTR_OR_BOTH_INT(a1, a2, 1);
    assume v4.value_is(v2.__ctobpl_const_18, res);
    assume v4.value_is(v2.__ctobpl_const_19, a1);
    assume v4.value_is(v2.__ctobpl_const_20, a2);
    goto label_12#2;

  label_11_case_1#2:
    assume v4.INT_EQ(op, 1);
    assume v4.value_is(v2.__ctobpl_const_11, op);
    goto label_13#2;

  label_13#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 27} true;
    res := v4.PLUS(a1, 1, a2);
    assume v4.value_is(v2.__ctobpl_const_15, res);
    assume v4.value_is(v2.__ctobpl_const_16, a1);
    assume v4.value_is(v2.__ctobpl_const_17, a2);
    goto label_12#2;

  label_11_case_0#2:
    assume v4.INT_NEQ(op, 1);
    assume v4.INT_NEQ(op, 2);
    assume v4.value_is(v2.__ctobpl_const_11, op);
    goto label_12#2;

  label_12#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 35} true;
    assert true;
    v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR[v4.result__EXPR(e) := res];
    assume v4.value_is(v2.__ctobpl_const_12, e);
    assume v4.value_is(v2.__ctobpl_const_13, v4.Mem_T.result__EXPR[v4.result__EXPR(e)]);
    assume v4.value_is(v2.__ctobpl_const_14, res);
    goto label_1#2;

  label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 36} true;
    return;
}



implementation v2.EvalEntry1(e_.1: int, outval_.1: int)
{
  var havoc_stringTemp: int;
  var condVal: int;
  var e: int;
  var outval: int;
  var tempBoogie0: int;
  var tempBoogie1: int;
  var tempBoogie2: int;
  var tempBoogie3: int;
  var tempBoogie4: int;
  var tempBoogie5: int;
  var tempBoogie6: int;
  var tempBoogie7: int;
  var tempBoogie8: int;
  var tempBoogie9: int;
  var tempBoogie10: int;
  var tempBoogie11: int;
  var tempBoogie12: int;
  var tempBoogie13: int;
  var tempBoogie14: int;
  var tempBoogie15: int;
  var tempBoogie16: int;
  var tempBoogie17: int;
  var tempBoogie18: int;
  var tempBoogie19: int;
  var __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume v4.INT_LT(e_.1, v4.alloc);
    assume v4.INT_LT(outval_.1, v4.alloc);
    e := 0;
    outval := 0;
    e := e_.1;
    outval := outval_.1;
    goto label_3#2;

  label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 40} true;
    call v2.Eval(e);
    assume v4.value_is(v2.__ctobpl_const_21, e);
    assume v4.value_is(v2.__ctobpl_const_22, e);
    goto label_6#2;

  label_6#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 41} true;
    assert true;
    assert true;
    v4.Mem_T.INT4 := v4.Mem_T.INT4[outval := v4.Mem_T.result__EXPR[v4.result__EXPR(e)]];
    assume v4.value_is(v2.__ctobpl_const_23, outval);
    assume v4.value_is(v2.__ctobpl_const_24, v4.Mem_T.INT4[outval]);
    assume v4.value_is(v2.__ctobpl_const_25, e);
    assume v4.value_is(v2.__ctobpl_const_26, v4.Mem_T.result__EXPR[v4.result__EXPR(e)]);
    goto label_1#2;

  label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 42} true;
    return;
}



implementation v2.EvalEntry2(e_.1: int)
{
  var havoc_stringTemp: int;
  var condVal: int;
  var e: int;
  var tempBoogie0: int;
  var tempBoogie1: int;
  var tempBoogie2: int;
  var tempBoogie3: int;
  var tempBoogie4: int;
  var tempBoogie5: int;
  var tempBoogie6: int;
  var tempBoogie7: int;
  var tempBoogie8: int;
  var tempBoogie9: int;
  var tempBoogie10: int;
  var tempBoogie11: int;
  var tempBoogie12: int;
  var tempBoogie13: int;
  var tempBoogie14: int;
  var tempBoogie15: int;
  var tempBoogie16: int;
  var tempBoogie17: int;
  var tempBoogie18: int;
  var tempBoogie19: int;
  var __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume v4.INT_LT(e_.1, v4.alloc);
    e := 0;
    e := e_.1;
    goto label_3#2;

  label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 46} true;
    call v2.Eval(e);
    assume v4.value_is(v2.__ctobpl_const_27, e);
    assume v4.value_is(v2.__ctobpl_const_28, e);
    goto label_1#2;

  label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 47} true;
    return;
}



implementation v2.__havoc_heapglobal_init()
{

  anon0#2:
    return;
}



type name;

type byte;

var Output_of_v2.Eval_v4.Mem_T.result__EXPR: [int]int;

var Output_of_v4.Eval_v4.Mem_T.result__EXPR: [int]int;

procedure EQ_v2.Eval__v4.Eval(e_.1: int) returns (AA_TEMP30: bool);
  modifies v4.Mem_T.result__EXPR, Output_of_v2.Eval_v4.Mem_T.result__EXPR, Output_of_v4.Eval_v4.Mem_T.result__EXPR;
  ensures AA_TEMP30;



implementation EQ_v2.Eval__v4.Eval(e_.1: int) returns (AA_TEMP30: bool)
{
  var AA_TEMP10: [int]int;
  var AA_TEMP00: [int]int;
  var inline$v2.Eval$0$havoc_stringTemp: int;
  var inline$v2.Eval$0$condVal: int;
  var inline$v2.Eval$0$a1: int;
  var inline$v2.Eval$0$a2: int;
  var inline$v2.Eval$0$e: int;
  var inline$v2.Eval$0$op: int;
  var inline$v2.Eval$0$res: int;
  var inline$v2.Eval$0$tempBoogie0: int;
  var inline$v2.Eval$0$tempBoogie1: int;
  var inline$v2.Eval$0$tempBoogie2: int;
  var inline$v2.Eval$0$tempBoogie3: int;
  var inline$v2.Eval$0$tempBoogie4: int;
  var inline$v2.Eval$0$tempBoogie5: int;
  var inline$v2.Eval$0$tempBoogie6: int;
  var inline$v2.Eval$0$tempBoogie7: int;
  var inline$v2.Eval$0$tempBoogie8: int;
  var inline$v2.Eval$0$tempBoogie9: int;
  var inline$v2.Eval$0$tempBoogie10: int;
  var inline$v2.Eval$0$tempBoogie11: int;
  var inline$v2.Eval$0$tempBoogie12: int;
  var inline$v2.Eval$0$tempBoogie13: int;
  var inline$v2.Eval$0$tempBoogie14: int;
  var inline$v2.Eval$0$tempBoogie15: int;
  var inline$v2.Eval$0$tempBoogie16: int;
  var inline$v2.Eval$0$tempBoogie17: int;
  var inline$v2.Eval$0$tempBoogie18: int;
  var inline$v2.Eval$0$tempBoogie19: int;
  var inline$v2.Eval$0$__havoc_dummy_return: int;
  var inline$v2.Eval$0$e_.1: int;
  var inline$v2.Eval$0$v4.Mem_T.result__EXPR: [int]int;
  var inline$v4.Eval$0$havoc_stringTemp: int;
  var inline$v4.Eval$0$condVal: int;
  var inline$v4.Eval$0$a1: int;
  var inline$v4.Eval$0$a2: int;
  var inline$v4.Eval$0$e: int;
  var inline$v4.Eval$0$op: int;
  var inline$v4.Eval$0$res: int;
  var inline$v4.Eval$0$result.UnsignedAdd$1: int;
  var inline$v4.Eval$0$result.UnsignedSub$2: int;
  var inline$v4.Eval$0$tempBoogie0: int;
  var inline$v4.Eval$0$tempBoogie1: int;
  var inline$v4.Eval$0$tempBoogie2: int;
  var inline$v4.Eval$0$tempBoogie3: int;
  var inline$v4.Eval$0$tempBoogie4: int;
  var inline$v4.Eval$0$tempBoogie5: int;
  var inline$v4.Eval$0$tempBoogie6: int;
  var inline$v4.Eval$0$tempBoogie7: int;
  var inline$v4.Eval$0$tempBoogie8: int;
  var inline$v4.Eval$0$tempBoogie9: int;
  var inline$v4.Eval$0$tempBoogie10: int;
  var inline$v4.Eval$0$tempBoogie11: int;
  var inline$v4.Eval$0$tempBoogie12: int;
  var inline$v4.Eval$0$tempBoogie13: int;
  var inline$v4.Eval$0$tempBoogie14: int;
  var inline$v4.Eval$0$tempBoogie15: int;
  var inline$v4.Eval$0$tempBoogie16: int;
  var inline$v4.Eval$0$tempBoogie17: int;
  var inline$v4.Eval$0$tempBoogie18: int;
  var inline$v4.Eval$0$tempBoogie19: int;
  var inline$v4.Eval$0$__havoc_dummy_return: int;
  var inline$v4.Eval$0$e_.1: int;
  var inline$v4.Eval$0$v4.Mem_T.result__EXPR: [int]int;

  AA_INSTR_EQ_BODY:
    AA_TEMP00 := v4.Mem_T.result__EXPR;
    goto inline$v2.Eval$0$Entry;

  inline$v2.Eval$0$Entry:
    inline$v2.Eval$0$e_.1 := e_.1;
    inline$v2.Eval$0$v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR;
    goto inline$v2.Eval$0$anon0#2;

  inline$v2.Eval$0$anon0#2:
    inline$v2.Eval$0$havoc_stringTemp := 0;
    goto inline$v2.Eval$0$start#2;

  inline$v2.Eval$0$start#2:
    assume v4.INT_LT(inline$v2.Eval$0$e_.1, v4.alloc);
    inline$v2.Eval$0$a1 := 0;
    inline$v2.Eval$0$a2 := 0;
    inline$v2.Eval$0$e := 0;
    inline$v2.Eval$0$op := 0;
    inline$v2.Eval$0$res := 0;
    inline$v2.Eval$0$e := inline$v2.Eval$0$e_.1;
    goto inline$v2.Eval$0$label_3#2;

  inline$v2.Eval$0$label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto inline$v2.Eval$0$label_4#2;

  inline$v2.Eval$0$label_4#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto inline$v2.Eval$0$label_5#2;

  inline$v2.Eval$0$label_5#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto inline$v2.Eval$0$label_6#2;

  inline$v2.Eval$0$label_6#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 17} true;
    goto inline$v2.Eval$0$label_7#2;

  inline$v2.Eval$0$label_7#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 19} true;
    assert true;
    inline$v2.Eval$0$op := v4.Mem_T.oper__EXPR[v4.oper__EXPR(inline$v2.Eval$0$e)];
    assume v4.value_is(v2.__ctobpl_const_1, inline$v2.Eval$0$op);
    assume v4.value_is(v2.__ctobpl_const_2, inline$v2.Eval$0$e);
    assume v4.value_is(v2.__ctobpl_const_3, v4.Mem_T.oper__EXPR[v4.oper__EXPR(inline$v2.Eval$0$e)]);
    goto inline$v2.Eval$0$label_8#2;

  inline$v2.Eval$0$label_8#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 20} true;
    assert true;
    inline$v2.Eval$0$a1 := v4.Mem_T.op1__EXPR[v4.op1__EXPR(inline$v2.Eval$0$e)];
    assume v4.value_is(v2.__ctobpl_const_4, inline$v2.Eval$0$a1);
    assume v4.value_is(v2.__ctobpl_const_5, inline$v2.Eval$0$e);
    assume v4.value_is(v2.__ctobpl_const_6, v4.Mem_T.op1__EXPR[v4.op1__EXPR(inline$v2.Eval$0$e)]);
    goto inline$v2.Eval$0$label_9#2;

  inline$v2.Eval$0$label_9#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 21} true;
    assert true;
    inline$v2.Eval$0$a2 := v4.Mem_T.op2__EXPR[v4.op2__EXPR(inline$v2.Eval$0$e)];
    assume v4.value_is(v2.__ctobpl_const_7, inline$v2.Eval$0$a2);
    assume v4.value_is(v2.__ctobpl_const_8, inline$v2.Eval$0$e);
    assume v4.value_is(v2.__ctobpl_const_9, v4.Mem_T.op2__EXPR[v4.op2__EXPR(inline$v2.Eval$0$e)]);
    goto inline$v2.Eval$0$label_10#2;

  inline$v2.Eval$0$label_10#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 22} true;
    inline$v2.Eval$0$res := 0 - 1;
    assume v4.value_is(v2.__ctobpl_const_10, inline$v2.Eval$0$res);
    goto inline$v2.Eval$0$label_11#2;

  inline$v2.Eval$0$label_11#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 24} true;
    goto inline$v2.Eval$0$label_11_case_0#2, inline$v2.Eval$0$label_11_case_1#2, inline$v2.Eval$0$label_11_case_2#2;

  inline$v2.Eval$0$label_11_case_2#2:
    assume v4.INT_EQ(inline$v2.Eval$0$op, 2);
    assume v4.value_is(v2.__ctobpl_const_11, inline$v2.Eval$0$op);
    goto inline$v2.Eval$0$label_14#2;

  inline$v2.Eval$0$label_14#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 29} true;
    inline$v2.Eval$0$res := v4.MINUS_BOTH_PTR_OR_BOTH_INT(inline$v2.Eval$0$a1, inline$v2.Eval$0$a2, 1);
    assume v4.value_is(v2.__ctobpl_const_18, inline$v2.Eval$0$res);
    assume v4.value_is(v2.__ctobpl_const_19, inline$v2.Eval$0$a1);
    assume v4.value_is(v2.__ctobpl_const_20, inline$v2.Eval$0$a2);
    goto inline$v2.Eval$0$label_12#2;

  inline$v2.Eval$0$label_11_case_1#2:
    assume v4.INT_EQ(inline$v2.Eval$0$op, 1);
    assume v4.value_is(v2.__ctobpl_const_11, inline$v2.Eval$0$op);
    goto inline$v2.Eval$0$label_13#2;

  inline$v2.Eval$0$label_13#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 27} true;
    inline$v2.Eval$0$res := v4.PLUS(inline$v2.Eval$0$a1, 1, inline$v2.Eval$0$a2);
    assume v4.value_is(v2.__ctobpl_const_15, inline$v2.Eval$0$res);
    assume v4.value_is(v2.__ctobpl_const_16, inline$v2.Eval$0$a1);
    assume v4.value_is(v2.__ctobpl_const_17, inline$v2.Eval$0$a2);
    goto inline$v2.Eval$0$label_12#2;

  inline$v2.Eval$0$label_11_case_0#2:
    assume v4.INT_NEQ(inline$v2.Eval$0$op, 1);
    assume v4.INT_NEQ(inline$v2.Eval$0$op, 2);
    assume v4.value_is(v2.__ctobpl_const_11, inline$v2.Eval$0$op);
    goto inline$v2.Eval$0$label_12#2;

  inline$v2.Eval$0$label_12#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 35} true;
    assert true;
    v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR[v4.result__EXPR(inline$v2.Eval$0$e) := inline$v2.Eval$0$res];
    assume v4.value_is(v2.__ctobpl_const_12, inline$v2.Eval$0$e);
    assume v4.value_is(v2.__ctobpl_const_13, v4.Mem_T.result__EXPR[v4.result__EXPR(inline$v2.Eval$0$e)]);
    assume v4.value_is(v2.__ctobpl_const_14, inline$v2.Eval$0$res);
    goto inline$v2.Eval$0$label_1#2;

  inline$v2.Eval$0$label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v2\foo.c"} {:sourceline 36} true;
    goto inline$v2.Eval$0$Return;

  inline$v2.Eval$0$Return:
    goto AA_INSTR_EQ_BODY$1;

  AA_INSTR_EQ_BODY$1:
    AA_TEMP10 := v4.Mem_T.result__EXPR;
    v4.Mem_T.result__EXPR := AA_TEMP00;
    goto inline$v4.Eval$0$Entry;

  inline$v4.Eval$0$Entry:
    inline$v4.Eval$0$e_.1 := e_.1;
    inline$v4.Eval$0$v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR;
    goto inline$v4.Eval$0$anon0#2;

  inline$v4.Eval$0$anon0#2:
    inline$v4.Eval$0$havoc_stringTemp := 0;
    goto inline$v4.Eval$0$start#2;

  inline$v4.Eval$0$start#2:
    assume v4.INT_LT(inline$v4.Eval$0$e_.1, v4.alloc);
    inline$v4.Eval$0$a1 := 0;
    inline$v4.Eval$0$a2 := 0;
    inline$v4.Eval$0$e := 0;
    inline$v4.Eval$0$op := 0;
    inline$v4.Eval$0$res := 0;
    inline$v4.Eval$0$result.UnsignedAdd$1 := 0;
    inline$v4.Eval$0$result.UnsignedSub$2 := 0;
    inline$v4.Eval$0$e := inline$v4.Eval$0$e_.1;
    goto inline$v4.Eval$0$label_3#2;

  inline$v4.Eval$0$label_3#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto inline$v4.Eval$0$label_4#2;

  inline$v4.Eval$0$label_4#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto inline$v4.Eval$0$label_5#2;

  inline$v4.Eval$0$label_5#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto inline$v4.Eval$0$label_6#2;

  inline$v4.Eval$0$label_6#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 19} true;
    goto inline$v4.Eval$0$label_7#2;

  inline$v4.Eval$0$label_7#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 21} true;
    assert true;
    inline$v4.Eval$0$op := v4.Mem_T.oper__EXPR[v4.oper__EXPR(inline$v4.Eval$0$e)];
    assume v4.value_is(v4.__ctobpl_const_1, inline$v4.Eval$0$op);
    assume v4.value_is(v4.__ctobpl_const_2, inline$v4.Eval$0$e);
    assume v4.value_is(v4.__ctobpl_const_3, v4.Mem_T.oper__EXPR[v4.oper__EXPR(inline$v4.Eval$0$e)]);
    goto inline$v4.Eval$0$label_8#2;

  inline$v4.Eval$0$label_8#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 22} true;
    assert true;
    inline$v4.Eval$0$a1 := v4.Mem_T.op1__EXPR[v4.op1__EXPR(inline$v4.Eval$0$e)];
    assume v4.value_is(v4.__ctobpl_const_4, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_5, inline$v4.Eval$0$e);
    assume v4.value_is(v4.__ctobpl_const_6, v4.Mem_T.op1__EXPR[v4.op1__EXPR(inline$v4.Eval$0$e)]);
    goto inline$v4.Eval$0$label_9#2;

  inline$v4.Eval$0$label_9#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 23} true;
    assert true;
    inline$v4.Eval$0$a2 := v4.Mem_T.op2__EXPR[v4.op2__EXPR(inline$v4.Eval$0$e)];
    assume v4.value_is(v4.__ctobpl_const_7, inline$v4.Eval$0$a2);
    assume v4.value_is(v4.__ctobpl_const_8, inline$v4.Eval$0$e);
    assume v4.value_is(v4.__ctobpl_const_9, v4.Mem_T.op2__EXPR[v4.op2__EXPR(inline$v4.Eval$0$e)]);
    goto inline$v4.Eval$0$label_10#2;

  inline$v4.Eval$0$label_10#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 24} true;
    inline$v4.Eval$0$res := 0 - 1;
    assume v4.value_is(v4.__ctobpl_const_10, inline$v4.Eval$0$res);
    goto inline$v4.Eval$0$label_11#2;

  inline$v4.Eval$0$label_11#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 26} true;
    goto inline$v4.Eval$0$label_11_case_0#2, inline$v4.Eval$0$label_11_case_1#2, inline$v4.Eval$0$label_11_case_2#2;

  inline$v4.Eval$0$label_11_case_2#2:
    assume v4.INT_EQ(inline$v4.Eval$0$op, 2);
    assume v4.value_is(v4.__ctobpl_const_11, inline$v4.Eval$0$op);
    goto inline$v4.Eval$0$label_14#2;

  inline$v4.Eval$0$label_14#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 35} true;
    goto inline$v4.Eval$0$label_14_true#2, inline$v4.Eval$0$label_14_false#2;

  inline$v4.Eval$0$label_14_false#2:
    assume v4.isUnsigned == 0;
    assume v4.value_is(v4.__ctobpl_const_16, v4.isUnsigned);
    goto inline$v4.Eval$0$label_15#2;

  inline$v4.Eval$0$label_15#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 38} true;
    inline$v4.Eval$0$res := v4.MINUS_BOTH_PTR_OR_BOTH_INT(inline$v4.Eval$0$a1, inline$v4.Eval$0$a2, 1);
    assume v4.value_is(v4.__ctobpl_const_17, inline$v4.Eval$0$res);
    assume v4.value_is(v4.__ctobpl_const_18, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_19, inline$v4.Eval$0$a2);
    goto inline$v4.Eval$0$label_12#2;

  inline$v4.Eval$0$label_14_true#2:
    assume v4.isUnsigned != 0;
    assume v4.value_is(v4.__ctobpl_const_16, v4.isUnsigned);
    goto inline$v4.Eval$0$label_16#2;

  inline$v4.Eval$0$label_16#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 36} true;
    call inline$v4.Eval$0$result.UnsignedSub$2 := v4.UnsignedSub(inline$v4.Eval$0$a1, inline$v4.Eval$0$a2);
    assume v4.value_is(v4.__ctobpl_const_20, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_21, inline$v4.Eval$0$a2);
    assume v4.value_is(v4.__ctobpl_const_22, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_23, inline$v4.Eval$0$a2);
    goto inline$v4.Eval$0$label_19#2;

  inline$v4.Eval$0$label_19#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 36} true;
    inline$v4.Eval$0$res := inline$v4.Eval$0$result.UnsignedSub$2;
    assume v4.value_is(v4.__ctobpl_const_24, inline$v4.Eval$0$res);
    assume v4.value_is(v4.__ctobpl_const_25, inline$v4.Eval$0$result.UnsignedSub$2);
    goto inline$v4.Eval$0$label_12#2;

  inline$v4.Eval$0$label_11_case_1#2:
    assume v4.INT_EQ(inline$v4.Eval$0$op, 1);
    assume v4.value_is(v4.__ctobpl_const_11, inline$v4.Eval$0$op);
    goto inline$v4.Eval$0$label_13#2;

  inline$v4.Eval$0$label_13#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 29} true;
    goto inline$v4.Eval$0$label_13_true#2, inline$v4.Eval$0$label_13_false#2;

  inline$v4.Eval$0$label_13_false#2:
    assume v4.isUnsigned == 0;
    assume v4.value_is(v4.__ctobpl_const_15, v4.isUnsigned);
    goto inline$v4.Eval$0$label_20#2;

  inline$v4.Eval$0$label_20#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 32} true;
    inline$v4.Eval$0$res := v4.PLUS(inline$v4.Eval$0$a1, 1, inline$v4.Eval$0$a2);
    assume v4.value_is(v4.__ctobpl_const_26, inline$v4.Eval$0$res);
    assume v4.value_is(v4.__ctobpl_const_27, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_28, inline$v4.Eval$0$a2);
    goto inline$v4.Eval$0$label_12#2;

  inline$v4.Eval$0$label_13_true#2:
    assume v4.isUnsigned != 0;
    assume v4.value_is(v4.__ctobpl_const_15, v4.isUnsigned);
    goto inline$v4.Eval$0$label_21#2;

  inline$v4.Eval$0$label_21#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 30} true;
    call inline$v4.Eval$0$result.UnsignedAdd$1 := v4.UnsignedAdd(inline$v4.Eval$0$a1, inline$v4.Eval$0$a2);
    assume v4.value_is(v4.__ctobpl_const_29, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_30, inline$v4.Eval$0$a2);
    assume v4.value_is(v4.__ctobpl_const_31, inline$v4.Eval$0$a1);
    assume v4.value_is(v4.__ctobpl_const_32, inline$v4.Eval$0$a2);
    goto inline$v4.Eval$0$label_24#2;

  inline$v4.Eval$0$label_24#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 30} true;
    inline$v4.Eval$0$res := inline$v4.Eval$0$result.UnsignedAdd$1;
    assume v4.value_is(v4.__ctobpl_const_33, inline$v4.Eval$0$res);
    assume v4.value_is(v4.__ctobpl_const_34, inline$v4.Eval$0$result.UnsignedAdd$1);
    goto inline$v4.Eval$0$label_12#2;

  inline$v4.Eval$0$label_11_case_0#2:
    assume v4.INT_NEQ(inline$v4.Eval$0$op, 1);
    assume v4.INT_NEQ(inline$v4.Eval$0$op, 2);
    assume v4.value_is(v4.__ctobpl_const_11, inline$v4.Eval$0$op);
    goto inline$v4.Eval$0$label_12#2;

  inline$v4.Eval$0$label_12#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 41} true;
    assert true;
    v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR[v4.result__EXPR(inline$v4.Eval$0$e) := inline$v4.Eval$0$res];
    assume v4.value_is(v4.__ctobpl_const_12, inline$v4.Eval$0$e);
    assume v4.value_is(v4.__ctobpl_const_13, v4.Mem_T.result__EXPR[v4.result__EXPR(inline$v4.Eval$0$e)]);
    assume v4.value_is(v4.__ctobpl_const_14, inline$v4.Eval$0$res);
    goto inline$v4.Eval$0$label_1#2;

  inline$v4.Eval$0$label_1#2:
    assert {:sourcefile "c:\tvm\projects\symb_diff\symdiff\test\c_examples\ex3\v4\foo.c"} {:sourceline 42} true;
    goto inline$v4.Eval$0$Return;

  inline$v4.Eval$0$Return:
    goto AA_INSTR_EQ_BODY$2;

  AA_INSTR_EQ_BODY$2:
    Output_of_v2.Eval_v4.Mem_T.result__EXPR := AA_TEMP10;
    Output_of_v4.Eval_v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR;
    AA_TEMP30 := AA_TEMP10 == v4.Mem_T.result__EXPR || (forall _x0: int :: AA_TEMP10[_x0] == v4.Mem_T.result__EXPR[_x0]);
    return;
}



var Output_of_v2.EvalEntry1_v4.Mem_T.result__EXPR: [int]int;

var Output_of_v4.EvalEntry1_v4.Mem_T.result__EXPR: [int]int;

var Output_of_v2.EvalEntry1_v4.Mem_T.INT4: [int]int;

var Output_of_v4.EvalEntry1_v4.Mem_T.INT4: [int]int;

var Output_of_v2.EvalEntry1_v4.isUnsigned: int;

var Output_of_v4.EvalEntry1_v4.isUnsigned: int;

procedure EQ_v2.EvalEntry1__v4.EvalEntry1(e_.1: int, outval_.1: int) returns (AA_TEMP80: bool, AA_TEMP81: bool, AA_TEMP82: bool);
  modifies v4.Mem_T.result__EXPR, v4.Mem_T.INT4, v4.isUnsigned, Output_of_v2.EvalEntry1_v4.Mem_T.result__EXPR, Output_of_v4.EvalEntry1_v4.Mem_T.result__EXPR, Output_of_v2.EvalEntry1_v4.Mem_T.INT4, Output_of_v4.EvalEntry1_v4.Mem_T.INT4, Output_of_v2.EvalEntry1_v4.isUnsigned, Output_of_v4.EvalEntry1_v4.isUnsigned;
  ensures AA_TEMP82 && AA_TEMP81 && AA_TEMP80;



implementation EQ_v2.EvalEntry1__v4.EvalEntry1(e_.1: int, outval_.1: int) returns (AA_TEMP80: bool, AA_TEMP81: bool, AA_TEMP82: bool)
{
  var AA_TEMP60: [int]int;
  var AA_TEMP61: [int]int;
  var AA_TEMP62: int;
  var AA_TEMP50: [int]int;
  var AA_TEMP51: [int]int;
  var AA_TEMP52: int;

  AA_INSTR_EQ_BODY:
    AA_TEMP50 := v4.Mem_T.result__EXPR;
    AA_TEMP51 := v4.Mem_T.INT4;
    AA_TEMP52 := v4.isUnsigned;
    call v2.EvalEntry1(e_.1, outval_.1);
    AA_TEMP60 := v4.Mem_T.result__EXPR;
    AA_TEMP61 := v4.Mem_T.INT4;
    AA_TEMP62 := v4.isUnsigned;
    v4.Mem_T.result__EXPR := AA_TEMP50;
    v4.Mem_T.INT4 := AA_TEMP51;
    v4.isUnsigned := AA_TEMP52;
    call v4.EvalEntry1(e_.1, outval_.1);
    Output_of_v2.EvalEntry1_v4.Mem_T.result__EXPR := AA_TEMP60;
    Output_of_v4.EvalEntry1_v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR;
    Output_of_v2.EvalEntry1_v4.Mem_T.INT4 := AA_TEMP61;
    Output_of_v4.EvalEntry1_v4.Mem_T.INT4 := v4.Mem_T.INT4;
    Output_of_v2.EvalEntry1_v4.isUnsigned := AA_TEMP62;
    Output_of_v4.EvalEntry1_v4.isUnsigned := v4.isUnsigned;
    AA_TEMP80, AA_TEMP81, AA_TEMP82 := AA_TEMP60 == v4.Mem_T.result__EXPR || (forall _x0: int :: AA_TEMP60[_x0] == v4.Mem_T.result__EXPR[_x0]), AA_TEMP61 == v4.Mem_T.INT4 || (forall _x0: int :: AA_TEMP61[_x0] == v4.Mem_T.INT4[_x0]), AA_TEMP62 == v4.isUnsigned;
    return;
}



var Output_of_v2.EvalEntry2_v4.Mem_T.result__EXPR: [int]int;

var Output_of_v4.EvalEntry2_v4.Mem_T.result__EXPR: [int]int;

var Output_of_v2.EvalEntry2_v4.isUnsigned: int;

var Output_of_v4.EvalEntry2_v4.isUnsigned: int;

procedure EQ_v2.EvalEntry2__v4.EvalEntry2(e_.1: int) returns (AA_TEMP130: bool, AA_TEMP131: bool);
  modifies v4.Mem_T.result__EXPR, v4.isUnsigned, Output_of_v2.EvalEntry2_v4.Mem_T.result__EXPR, Output_of_v4.EvalEntry2_v4.Mem_T.result__EXPR, Output_of_v2.EvalEntry2_v4.isUnsigned, Output_of_v4.EvalEntry2_v4.isUnsigned;
  ensures AA_TEMP131 && AA_TEMP130;



implementation EQ_v2.EvalEntry2__v4.EvalEntry2(e_.1: int) returns (AA_TEMP130: bool, AA_TEMP131: bool)
{
  var AA_TEMP110: [int]int;
  var AA_TEMP111: int;
  var AA_TEMP100: [int]int;
  var AA_TEMP101: int;

  AA_INSTR_EQ_BODY:
    AA_TEMP100 := v4.Mem_T.result__EXPR;
    AA_TEMP101 := v4.isUnsigned;
    call v2.EvalEntry2(e_.1);
    AA_TEMP110 := v4.Mem_T.result__EXPR;
    AA_TEMP111 := v4.isUnsigned;
    v4.Mem_T.result__EXPR := AA_TEMP100;
    v4.isUnsigned := AA_TEMP101;
    call v4.EvalEntry2(e_.1);
    Output_of_v2.EvalEntry2_v4.Mem_T.result__EXPR := AA_TEMP110;
    Output_of_v4.EvalEntry2_v4.Mem_T.result__EXPR := v4.Mem_T.result__EXPR;
    Output_of_v2.EvalEntry2_v4.isUnsigned := AA_TEMP111;
    Output_of_v4.EvalEntry2_v4.isUnsigned := v4.isUnsigned;
    AA_TEMP130, AA_TEMP131 := AA_TEMP110 == v4.Mem_T.result__EXPR || (forall _x0: int :: AA_TEMP110[_x0] == v4.Mem_T.result__EXPR[_x0]), AA_TEMP111 == v4.isUnsigned;
    return;
}



function _uf_v4.__HAVOC_malloc_new(arg_0: int) : int;

function _uf_v2.__HAVOC_malloc_new(arg_0: int) : int;

function _uf_v4.__HAVOC_det_malloc_new(arg_0: int) : int;

function _uf_v2.__HAVOC_det_malloc_new(arg_0: int) : int;

function _uf_v4.__HAVOC_memset_split_1_ret(arg_0: [int]int, arg_1: int, arg_2: int, arg_3: int) : [int]int;

function _uf_v2.__HAVOC_memset_split_1_ret(arg_0: [int]int, arg_1: int, arg_2: int, arg_3: int) : [int]int;

function _uf_v4.__HAVOC_memset_split_2_ret(arg_0: [int]int, arg_1: int, arg_2: int, arg_3: int) : [int]int;

function _uf_v2.__HAVOC_memset_split_2_ret(arg_0: [int]int, arg_1: int, arg_2: int, arg_3: int) : [int]int;

function _uf_v4.__HAVOC_memset_split_4_ret(arg_0: [int]int, arg_1: int, arg_2: int, arg_3: int) : [int]int;

function _uf_v2.__HAVOC_memset_split_4_ret(arg_0: [int]int, arg_1: int, arg_2: int, arg_3: int) : [int]int;

function _uf_v4.nondet_choice_x() : int;

function _uf_v2.nondet_choice_x() : int;

function _uf_v4.det_choice_x() : int;

function _uf_v2.det_choice_x() : int;

function _uf_v4._strdup_new(arg_0: int) : int;

function _uf_v2._strdup_new(arg_0: int) : int;

function _uf_v4._xstrcasecmp_ret(arg_0: int, arg_1: int) : int;

function _uf_v2._xstrcasecmp_ret(arg_0: int, arg_1: int) : int;

function _uf_v4._xstrcmp_ret(arg_0: int, arg_1: int) : int;

function _uf_v2._xstrcmp_ret(arg_0: int, arg_1: int) : int;

function _uf_v4.Eval_v4.Mem_T.result__EXPR(arg_0: int, arg_1: int, arg_2: [int]int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: int) : [int]int;

function _uf_v2.Eval_v4.Mem_T.result__EXPR(arg_0: int, arg_1: int, arg_2: [int]int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: int) : [int]int;

function _uf_v4.EvalEntry1_v4.Mem_T.result__EXPR(arg_0: int, arg_1: int, arg_2: int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: [int]int, arg_7: [int]int, arg_8: int) : [int]int;

function _uf_v4.EvalEntry1_v4.Mem_T.INT4(arg_0: int, arg_1: int, arg_2: int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: [int]int, arg_7: [int]int, arg_8: int) : [int]int;

function _uf_v4.EvalEntry1_v4.isUnsigned(arg_0: int, arg_1: int, arg_2: int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: [int]int, arg_7: [int]int, arg_8: int) : int;

function _uf_v2.EvalEntry1_v4.Mem_T.result__EXPR(arg_0: int, arg_1: int, arg_2: int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: [int]int, arg_7: [int]int, arg_8: int) : [int]int;

function _uf_v2.EvalEntry1_v4.Mem_T.INT4(arg_0: int, arg_1: int, arg_2: int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: [int]int, arg_7: [int]int, arg_8: int) : [int]int;

function _uf_v4.EvalEntry2_v4.Mem_T.result__EXPR(arg_0: int, arg_1: int, arg_2: [int]int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: int) : [int]int;

function _uf_v4.EvalEntry2_v4.isUnsigned(arg_0: int, arg_1: int, arg_2: [int]int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: int) : int;

function _uf_v2.EvalEntry2_v4.Mem_T.result__EXPR(arg_0: int, arg_1: int, arg_2: [int]int, arg_3: [int]int, arg_4: [int]int, arg_5: [int]int, arg_6: int) : [int]int;
