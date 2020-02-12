// RUN: %boogie /nologo /contractInfer /inlineDepth:1 /printAssignment /noinfer  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function _v2.ite(b: bool, x: int, y: int) : int;

var _v2.OK: bool;

var {:extern} _v2.Mem: [name][int]int;

var {:extern} _v2.alloc: int;

var {:extern} _v2.Mem_T.A1CHAR: [int]int;

var {:extern} _v2.Mem_T.A5UCHAR: [int]int;

var {:extern} _v2.Mem_T.A6UCHAR: [int]int;

var {:extern} _v2.Mem_T.CHAR: [int]int;

var {:extern} _v2.Mem_T.INT4: [int]int;

var {:extern} _v2.Mem_T.PCHAR: [int]int;

var {:extern} _v2.Mem_T.PUCHAR: [int]int;

var {:extern} _v2.Mem_T.PVOID: [int]int;

var {:extern} _v2.Mem_T.Pieee80211_scan_entry: [int]int;

var {:extern} _v2.Mem_T.UCHAR: [int]int;

var {:extern} _v2.Mem_T.VOID: [int]int;

var {:extern} _v2.Mem_T.ieee80211_scan_entry: [int]int;

var {:extern} _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;

var {:extern} _v2.detChoiceCnt: int;

var {:extern} _v2.Res_KERNEL_SOURCE: [int]int;

var {:extern} _v2.Res_PROBED: [int]int;

const {:extern} unique _v2.T.se_rsn_ie_ieee80211_scan_entry: name;

const {:extern} unique _v2.T.A1CHAR: name;

const {:extern} unique _v2.T.A5UCHAR: name;

const {:extern} unique _v2.T.A6UCHAR: name;

const {:extern} unique _v2.T.CHAR: name;

const {:extern} unique _v2.T.INT4: name;

const {:extern} unique _v2.T.PA1CHAR: name;

const {:extern} unique _v2.T.PA5UCHAR: name;

const {:extern} unique _v2.T.PA6UCHAR: name;

const {:extern} unique _v2.T.PCHAR: name;

const {:extern} unique _v2.T.PINT4: name;

const {:extern} unique _v2.T.PPCHAR: name;

const {:extern} unique _v2.T.PPUCHAR: name;

const {:extern} unique _v2.T.PPVOID: name;

const {:extern} unique _v2.T.PPieee80211_scan_entry: name;

const {:extern} unique _v2.T.PUCHAR: name;

const {:extern} unique _v2.T.PUINT4: name;

const {:extern} unique _v2.T.PVOID: name;

const {:extern} unique _v2.T.Pieee80211_scan_entry: name;

const {:extern} unique _v2.T.UCHAR: name;

const {:extern} unique _v2.T.UINT4: name;

const {:extern} unique _v2.T.VOID: name;

const {:extern} unique _v2.T.ieee80211_scan_entry: name;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 16} unique _v2.__ctobpl_const_8: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 13} unique _v2.__ctobpl_const_2: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 15} unique _v2.__ctobpl_const_3: int;

const {:extern} {:model_const "buf"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 15} unique _v2.__ctobpl_const_4: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 16} unique _v2.__ctobpl_const_5: int;

const {:extern} {:model_const "leader"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 16} unique _v2.__ctobpl_const_6: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 16} unique _v2.__ctobpl_const_7: int;

const {:extern} {:model_const "leader"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 16} unique _v2.__ctobpl_const_9: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 16} unique _v2.__ctobpl_const_10: int;

const {:extern} {:model_const "encode_ie.arg.4"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 53} unique _v2.__ctobpl_const_44: int;

const {:extern} {:model_const "(se.se_rsn_ie)[0]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 66} unique _v2.__ctobpl_const_50: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 51} unique _v2.__ctobpl_const_34: int;

const {:extern} {:model_const "se.se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 67} unique _v2.__ctobpl_const_51: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 53} unique _v2.__ctobpl_const_45: int;

const {:extern} {:model_const "(se.se_rsn_ie)[1]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 67} unique _v2.__ctobpl_const_52: int;

const {:extern} {:model_const "(se->se_rsn_ie)[0]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 52} unique _v2.__ctobpl_const_37: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 53} unique _v2.__ctobpl_const_42: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 54} unique _v2.__ctobpl_const_39: int;

const {:extern} {:model_const "encode_ie.arg.4"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 53} unique _v2.__ctobpl_const_47: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 54} unique _v2.__ctobpl_const_40: int;

const {:extern} {:model_const "encode_ie.arg.4"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 54} unique _v2.__ctobpl_const_38: int;

const {:extern} {:model_const "se.se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 66} unique _v2.__ctobpl_const_49: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 52} unique _v2.__ctobpl_const_35: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 53} unique _v2.__ctobpl_const_43: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 53} unique _v2.__ctobpl_const_46: int;

const {:extern} {:model_const "se.se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 65} unique _v2.__ctobpl_const_48: int;

const {:extern} {:model_const "(se->se_rsn_ie)[1]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 54} unique _v2.__ctobpl_const_41: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 52} unique _v2.__ctobpl_const_36: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 13} unique _v2.__ctobpl_const_1: int;

const {:extern} {:model_const "buf"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_31: int;

const {:extern} {:model_const "ielen"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 20} unique _v2.__ctobpl_const_17: int;

const {:extern} {:model_const "*(p + 1)"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 32} unique _v2.__ctobpl_const_24: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_18: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 34} unique _v2.__ctobpl_const_26: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 18} unique _v2.__ctobpl_const_14: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 20} unique _v2.__ctobpl_const_27: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 51} unique _v2.__ctobpl_const_33: int;

const {:extern} {:model_const "result.question.3"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_28: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 20} unique _v2.__ctobpl_const_15: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 17} unique _v2.__ctobpl_const_11: int;

const {:extern} {:model_const "result.question.3"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_29: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 17} unique _v2.__ctobpl_const_12: int;

const {:extern} {:model_const "result.question.3"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_32: int;

const {:extern} {:model_const "ielen"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_19: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 30} unique _v2.__ctobpl_const_21: int;

const {:extern} {:model_const "*p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 30} unique _v2.__ctobpl_const_22: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 32} unique _v2.__ctobpl_const_23: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 20} unique _v2.__ctobpl_const_16: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 20} unique _v2.__ctobpl_const_20: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 33} unique _v2.__ctobpl_const_25: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 18} unique _v2.__ctobpl_const_13: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceLine 39} unique _v2.__ctobpl_const_30: int;

function {:extern} _v2.OneByteToInt(arg_0: byte) : int;

function {:extern} _v2.TwoBytesToInt(arg_0: byte, arg_1: byte) : int;

function {:extern} _v2.FourBytesToInt(arg_0: byte, arg_1: byte, arg_2: byte, arg_3: byte) : int;

function {:extern} _v2.Field(arg_0: int) : name;

function {:extern} _v2.Base(arg_0: int) : int;

function {:extern} _v2.Match(a: int, t: name) : bool;

function {:extern} _v2.MatchBase(b: int, a: int, t: name) : bool;

function {:extern} _v2.HasType(v: int, t: name) : bool;

function {:extern} _v2.T.Ptr(t: name) : name;

function {:extern} _v2.se_rsn_ie_ieee80211_scan_entry(arg_0: int) : int;

function {:extern} _v2.se_rsn_ie_ieee80211_scan_entryInv(arg_0: int) : int;

function {:extern} _v2._S_se_rsn_ie_ieee80211_scan_entry(arg_0: [int]bool) : [int]bool;

function {:extern} _v2._S_se_rsn_ie_ieee80211_scan_entryInv(arg_0: [int]bool) : [int]bool;

function {:extern} _v2.INT_AND(a: int, b: int) : int;

function {:extern} _v2.INT_OR(a: int, b: int) : int;

function {:extern} _v2.INT_XOR(a: int, b: int) : int;

function {:extern} _v2.INT_NOT(a: int) : int;

function {:extern} _v2.POW2(a: int) : bool;

function {:extern} _v2.INT_MINUS_LEFT_PTR(a: int, a_size: int, b: int) : int;

function {:extern} _v2.INT_PLUS(a: int, a_size: int, b: int) : int;

function {:extern} _v2.INT_MULT(a: int, b: int) : int;

function {:extern} _v2.INT_DIV(a: int, b: int) : int;

function {:extern} _v2.INT_BINARY_BOTH_INT(a: int, b: int) : int;

function {:extern} _v2.BV32_EQ(x: bv32, y: bv32) : bool;

function {:extern} _v2.BV32_NEQ(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvadd"} _v2.BV32_ADD(x: bv32, y: bv32) : bv32;

function {:extern} {:bvbuiltin "bvsub"} _v2.BV32_SUB(x: bv32, y: bv32) : bv32;

function {:extern} {:bvbuiltin "bvmul"} _v2.BV32_MULT(x: bv32, y: bv32) : bv32;

function {:extern} {:bvbuiltin "bvudiv"} _v2.BV32_DIV(x: bv32, y: bv32) : bv32;

function {:extern} {:bvbuiltin "bvult"} _v2.BV32_ULT(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvslt"} _v2.BV32_LT(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvule"} _v2.BV32_ULEQ(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvsle"} _v2.BV32_LEQ(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvugt"} _v2.BV32_UGT(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvsgt"} _v2.BV32_GT(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvuge"} _v2.BV32_UGEQ(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvsge"} _v2.BV32_GEQ(x: bv32, y: bv32) : bool;

function {:extern} {:bvbuiltin "bvand"} _v2.BV32_AND(a: bv32, b: bv32) : bv32;

function {:extern} {:bvbuiltin "bvor"} _v2.BV32_OR(a: bv32, b: bv32) : bv32;

function {:extern} {:bvbuiltin "bvxor"} _v2.BV32_XOR(a: bv32, b: bv32) : bv32;

function {:extern} {:bvbuiltin "bvnot"} _v2.BV32_NOT(a: bv32) : bv32;

function {:extern} _v2.BV32_MINUS_BOTH_PTR_OR_BOTH_INT(a: bv32, b: bv32, size: bv32) : bv32;

function {:extern} _v2.BV32_MINUS_LEFT_PTR(a: bv32, a_size: bv32, b: bv32) : bv32;

function {:extern} _v2.BV32_PLUS(a: bv32, a_size: bv32, b: bv32) : bv32;

function {:extern} _v2.BV32_BINARY_BOTH_INT(a: bv32, b: bv32) : bv32;

function {:extern} _v2.bv32ToInt(arg_0: bv32) : int;

function {:extern} _v2.intToBv32(arg_0: int) : bv32;

function {:extern} _v2.choose(a: bool, b: int, c: int) : int;

function {:extern} _v2.LIFT(a: bool) : int;

function {:extern} _v2.PTR_NOT(a: int) : int;

function {:extern} _v2.NULL_CHECK(a: int) : int;

function {:extern} _v2.NewAlloc(x: int, y: int) : int;

function {:extern} _v2.DetChoiceFunc(a: int) : int;

function {:extern} _v2.Res_VALID_REGION(arg_0: int) : int;

function {:extern} _v2.Equal(arg_0: [int]bool, arg_1: [int]bool) : bool;

function {:extern} _v2.Subset(arg_0: [int]bool, arg_1: [int]bool) : bool;

function {:extern} _v2.Disjoint(arg_0: [int]bool, arg_1: [int]bool) : bool;

function {:extern} _v2.Empty() : [int]bool;

function {:extern} _v2.SetTrue() : [int]bool;

function {:extern} _v2.Singleton(arg_0: int) : [int]bool;

function {:extern} _v2.Reachable(arg_0: [int,int]bool, arg_1: int) : [int]bool;

function {:extern} _v2.Union(arg_0: [int]bool, arg_1: [int]bool) : [int]bool;

function {:extern} _v2.Intersection(arg_0: [int]bool, arg_1: [int]bool) : [int]bool;

function {:extern} _v2.Difference(arg_0: [int]bool, arg_1: [int]bool) : [int]bool;

function {:extern} _v2.Dereference(arg_0: [int]bool, arg_1: [int]int) : [int]bool;

function {:extern} _v2.Inverse(f: [int]int, x: int) : [int]bool;

function {:extern} _v2.AtLeast(arg_0: int, arg_1: int) : [int]bool;

function {:extern} _v2.Rep(arg_0: int, arg_1: int) : int;

function {:extern} _v2.Array(arg_0: int, arg_1: int, arg_2: int) : [int]bool;

function {:extern} _v2.Unified(arg_0: [name][int]int) : [int]int;

function {:extern} _v2.value_is(c: int, e: int) : bool;


function {:inline true} _v2.se_rsn_ie_ieee80211_scan_entry(x : int) : int
{
_v2.INT_ADD(x, 0)
}

function {:inline true} _v2.INT_EQ(x : int, y : int): bool 
{
x == y
}

function {:inline true} _v2.INT_NEQ(x : int, y: int): bool 
{
x != y
}

function {:inline true} _v2.INT_ADD(x : int, y : int): int 
{
x + y
}

function {:inline true}   _v2.INT_SUB(x : int, y : int): int
{
 x - y
}

function {:inline true}   _v2.INT_LT(x : int, y : int): bool 
{
x < y
}

function {:inline true}   _v2.INT_ULT(x : int, y : int): bool 
{
x < y
}

function {:inline true}   _v2.INT_LEQ(x : int, y : int): bool 
{
x <= y
}

function {:inline true}   _v2.INT_ULEQ(x : int, y : int): bool 
{
x <= y
}

function {:inline true}   _v2.INT_GT(x : int, y : int): bool 
{
x > y
}

function {:inline true}   _v2.INT_UGT(x : int, y : int): bool 
{
x > y
}

function {:inline true}   _v2.INT_GEQ(x : int, y : int): bool 
{
x >= y
}

function {:inline true}   _v2.INT_UGEQ(x : int, y : int): bool 
{
x >= y
}



procedure _v2.havoc_assert(i: int);
  /* free */ requires i != 0;
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.havoc_assume(i: int);
  /* free */ ensures i != 0;
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.__HAVOC_free(a: int);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.__HAVOC_malloc(obj_size: int) returns (new: int);
  /* free */ requires _v2.INT_GEQ(obj_size, 0);
  modifies _v2.alloc;
  /* free */ ensures new == old(_v2.alloc);
  /* free */ ensures _v2.INT_GT(_v2.alloc, _v2.INT_ADD(new, obj_size));
  /* free */ ensures _v2.Base(new) == new;
  /* free */ ensures _v2.INT_GEQ(new, 0);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.__HAVOC_det_malloc(obj_size: int) returns (new: int);
  /* free */ requires _v2.INT_GEQ(obj_size, 0);
  modifies _v2.alloc;
  /* free */ ensures new == old(_v2.alloc);
  /* free */ ensures _v2.INT_GT(_v2.alloc, _v2.INT_ADD(new, obj_size));
  /* free */ ensures _v2.Base(new) == new;
  /* free */ ensures _v2.alloc == _v2.NewAlloc(old(_v2.alloc), obj_size);
  /* free */ ensures _v2.INT_GEQ(new, 0);
  /* free */ ensures _v2.OK ==> old(_v2.OK);




procedure _v2.nondet_choice() returns (x: int);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.det_choice() returns (x: int);
  modifies _v2.detChoiceCnt;
  /* free */ ensures _v2.detChoiceCnt == _v2.INT_ADD(old(_v2.detChoiceCnt), 1);
  /* free */ ensures x == _v2.DetChoiceFunc(old(_v2.detChoiceCnt));
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2._strdup(str: int) returns (new: int);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2._xstrcasecmp(a0: int, a1: int) returns (ret: int);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2._xstrcmp(a0: int, a1: int) returns (ret: int);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.memcpy(a0: int, a1: int, a2: int) returns (ret: int);
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.encode_ie(buf_.1: int, 
    bufsize_.1: int, 
    ie_.1: int, 
    ielen_.1: int, 
    leader_.1: int, 
    leader_len_.1: int)
   returns (result.encode_ie$1: int);
  modifies _v2.OK, _v2.Mem_T.UCHAR;
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.giwscan_cb(se_.1: int) returns (result.giwscan_cb$1: int);
  modifies _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.main() returns (result.main$1: int);
  modifies _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
  /* free */ ensures _v2.OK ==> old(_v2.OK);



procedure _v2.encode_ie_loop_label_14_head(in_bufsize: int, in_i: int, in_ielen: int, in_p: int, in_tempBoogie0: int)
   returns (out_bufsize: int, out_i: int, out_p: int, out_tempBoogie0: int);
  modifies _v2.Mem_T.UCHAR, _v2.OK;
  /* free */ ensures _v2.OK ==> old(_v2.OK);



implementation _v2.encode_ie(buf_.1: int, 
    bufsize_.1: int, 
    ie_.1: int, 
    ielen_.1: int, 
    leader_.1: int, 
    leader_len_.1: int)
   returns (result.encode_ie$1: int)
{
  var {:extern} havoc_stringTemp: int;
  var {:extern} condVal: int;
  var {:extern} buf: int;
  var {:extern} bufsize: int;
  var {:extern} i: int;
  var {:extern} ie: int;
  var {:extern} ielen: int;
  var {:extern} leader: int;
  var {:extern} leader_len: int;
  var {:extern} p: int;
  var {:extern} result.memcpy$2: int;
  var {:extern} $result.question.3.$$static$: int;
  var {:extern} tempBoogie0: int;
  var {:extern} tempBoogie1: int;
  var {:extern} tempBoogie2: int;
  var {:extern} tempBoogie3: int;
  var {:extern} tempBoogie4: int;
  var {:extern} tempBoogie5: int;
  var {:extern} tempBoogie6: int;
  var {:extern} tempBoogie7: int;
  var {:extern} tempBoogie8: int;
  var {:extern} tempBoogie9: int;
  var {:extern} tempBoogie10: int;
  var {:extern} tempBoogie11: int;
  var {:extern} tempBoogie12: int;
  var {:extern} tempBoogie13: int;
  var {:extern} tempBoogie14: int;
  var {:extern} tempBoogie15: int;
  var {:extern} tempBoogie16: int;
  var {:extern} tempBoogie17: int;
  var {:extern} tempBoogie18: int;
  var {:extern} tempBoogie19: int;
  var {:extern} __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume _v2.INT_LT(buf_.1, _v2.alloc);
    assume _v2.INT_LT(ie_.1, _v2.alloc);
    assume _v2.INT_LT(leader_.1, _v2.alloc);
    buf := 0;
    assume _v2.INT_GEQ(buf_.1, 0);
    bufsize := 0;
    i := 0;
    ie := 0;
    assume _v2.INT_GEQ(ie_.1, 0);
    ielen := 0;
    leader := 0;
    assume _v2.INT_GEQ(leader_.1, 0);
    leader_len := 0;
    p := 0;
    result.encode_ie$1 := 0;
    result.memcpy$2 := 0;
    $result.question.3.$$static$ := 0;
    buf := buf_.1;
    bufsize := bufsize_.1;
    ie := ie_.1;
    ielen := ielen_.1;
    leader := leader_.1;
    leader_len := leader_len_.1;
    goto label_3#2;

  label_3#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 9} true;
    goto label_4#2;

  label_4#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 10} true;
    goto label_5#2;

  label_5#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 13} true;
    goto label_5_true#2, label_5_false#2;

  label_5_false#2:
    assume !_v2.INT_LT(bufsize, leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_1, bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_2, leader_len);
    goto label_6#2;

  label_6#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 15} true;
    p := buf;
    assume _v2.value_is(_v2.__ctobpl_const_3, p);
    assume _v2.value_is(_v2.__ctobpl_const_4, buf);
    goto label_8#2;

  label_8#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 16} true;
    call result.memcpy$2 := _v2.memcpy(p, leader, leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_5, p);
    assume _v2.value_is(_v2.__ctobpl_const_6, leader);
    assume _v2.value_is(_v2.__ctobpl_const_7, leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_8, p);
    assume _v2.value_is(_v2.__ctobpl_const_9, leader);
    assume _v2.value_is(_v2.__ctobpl_const_10, leader_len);
    goto label_11#2;

  label_11#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 17} true;
    havoc tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(bufsize, leader_len, 1, tempBoogie0);
    bufsize := tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_11, bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_12, leader_len);
    goto label_12#2;

  label_12#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 18} true;
    tempBoogie0 := _v2.INT_PLUS(p, 1, leader_len);
    p := tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_13, p);
    assume _v2.value_is(_v2.__ctobpl_const_14, leader_len);
    goto label_13#2;

  label_13#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    i := 0;
    assume _v2.value_is(_v2.__ctobpl_const_15, i);
    goto label_14#2;

  label_14#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    goto label_14_head#2;

  label_14_head#2:
    call bufsize, i, p, tempBoogie0 := _v2.encode_ie_loop_label_14_head(bufsize, i, ielen, p, tempBoogie0);
    goto label_14_head_last#2;

  label_14_head_last#2:
    goto label_14_true#2, label_14_false#2;

  label_14_false#2:
    assume !_v2.INT_LT(i, ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, i);
    assume _v2.value_is(_v2.__ctobpl_const_17, ielen);
    goto label_15#2;

  label_14_true#2:
    assume _v2.INT_LT(i, ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, i);
    assume _v2.value_is(_v2.__ctobpl_const_17, ielen);
    goto label_16#2;

  label_16#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    goto label_16_true#2, label_16_false#2;

  label_16_false#2:
    assume !_v2.INT_LT(2, bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, bufsize);
    goto label_15#2;

  label_15#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    goto label_15_true#2, label_15_false#2;

  label_15_false#2:
    assume !_v2.INT_EQ(i, ielen);
    assume _v2.value_is(_v2.__ctobpl_const_18, i);
    assume _v2.value_is(_v2.__ctobpl_const_19, ielen);
    goto label_22#2;

  label_22#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    $result.question.3.$$static$ := 0;
    assume _v2.value_is(_v2.__ctobpl_const_28, $result.question.3.$$static$);
    goto label_24#2;

  label_15_true#2:
    assume _v2.INT_EQ(i, ielen);
    assume _v2.value_is(_v2.__ctobpl_const_18, i);
    assume _v2.value_is(_v2.__ctobpl_const_19, ielen);
    goto label_23#2;

  label_23#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    havoc $result.question.3.$$static$;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(p, buf, 1, $result.question.3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_29, $result.question.3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_30, p);
    assume _v2.value_is(_v2.__ctobpl_const_31, buf);
    goto label_24#2;

  label_24#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    result.encode_ie$1 := $result.question.3.$$static$;
    assume _v2.value_is(_v2.__ctobpl_const_32, $result.question.3.$$static$);
    goto label_1#2;

  label_16_true#2:
    assume _v2.INT_LT(2, bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, bufsize);
    goto label_17#2;

  label_17#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(p, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(p) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[p := 120];
    assume _v2.value_is(_v2.__ctobpl_const_21, p);
    assume _v2.value_is(_v2.__ctobpl_const_22, _v2.Mem_T.UCHAR[p]);
    goto label_18#2;

  label_18#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(p, 1, 1), 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.INT_PLUS(p, 1, 1)) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(p, 1, 1) := 120];
    assume _v2.value_is(_v2.__ctobpl_const_23, p);
    assume _v2.value_is(_v2.__ctobpl_const_24, _v2.Mem_T.UCHAR[_v2.INT_PLUS(p, 1, 1)]);
    goto label_19#2;

  label_19#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 33} true;
    tempBoogie0 := _v2.INT_PLUS(p, 1, 2);
    p := tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_25, p);
    goto label_20#2;

  label_20#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 34} true;
    havoc tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(bufsize, 2, 1, tempBoogie0);
    bufsize := tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_26, bufsize);
    goto label_21#2;

  label_21#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    assume _v2.value_is(_v2.__ctobpl_const_27, i);
    i := _v2.INT_PLUS(i, 1, 1);
    goto label_21_dummy#2;

  label_21_dummy#2:
    assume false;
    return;

  label_5_true#2:
    assume _v2.INT_LT(bufsize, leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_1, bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_2, leader_len);
    goto label_7#2;

  label_7#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 14} true;
    result.encode_ie$1 := 0;
    goto label_1#2;

  label_1#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 40} true;
    return;
}



implementation _v2.giwscan_cb(se_.1: int) returns (result.giwscan_cb$1: int)
{
  var {:extern} havoc_stringTemp: int;
  var {:extern} condVal: int;
  var {:extern} buf: int;
  var {:extern} $encode_ie.arg.4$3.$$static$: int;
  var {:extern} result.encode_ie$2: int;
  var {:extern} rsn_leader: int;
  var {:extern} se: int;
  var {:extern} tempBoogie0: int;
  var {:extern} tempBoogie1: int;
  var {:extern} tempBoogie2: int;
  var {:extern} tempBoogie3: int;
  var {:extern} tempBoogie4: int;
  var {:extern} tempBoogie5: int;
  var {:extern} tempBoogie6: int;
  var {:extern} tempBoogie7: int;
  var {:extern} tempBoogie8: int;
  var {:extern} tempBoogie9: int;
  var {:extern} tempBoogie10: int;
  var {:extern} tempBoogie11: int;
  var {:extern} tempBoogie12: int;
  var {:extern} tempBoogie13: int;
  var {:extern} tempBoogie14: int;
  var {:extern} tempBoogie15: int;
  var {:extern} tempBoogie16: int;
  var {:extern} tempBoogie17: int;
  var {:extern} tempBoogie18: int;
  var {:extern} tempBoogie19: int;
  var {:extern} __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume _v2.INT_LT(se_.1, _v2.alloc);
    call buf := _v2.__HAVOC_det_malloc(6);
    $encode_ie.arg.4$3.$$static$ := 0;
    result.encode_ie$2 := 0;
    result.giwscan_cb$1 := 0;
    call rsn_leader := _v2.__HAVOC_det_malloc(1);
    se := 0;
    assume _v2.INT_GEQ(se_.1, 0);
    se := se_.1;
    goto label_3#2;

  label_3#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 46} true;
    goto label_4#2;

  label_4#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 47} true;
    goto label_5#2;

  label_5#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 51} true;
    assume _v2.INT_GEQ(se, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    goto label_5_true#2, label_5_false#2;

  label_5_false#2:
    assume _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]
   == 0;
    assume _v2.value_is(_v2.__ctobpl_const_33, se);
    assume _v2.value_is(_v2.__ctobpl_const_34, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    goto label_6#2;

  label_5_true#2:
    assume _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]
   != 0;
    assume _v2.value_is(_v2.__ctobpl_const_33, se);
    assume _v2.value_is(_v2.__ctobpl_const_34, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    goto label_7#2;

  label_7#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 52} true;
    assume _v2.INT_GEQ(se, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        0))
     == 1;
    assert true;
    goto label_7_true#2, label_7_false#2;

  label_7_false#2:
    assume !_v2.INT_EQ(_v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v2.__ctobpl_const_35, se);
    assume _v2.value_is(_v2.__ctobpl_const_36, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_37, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)]);
    goto label_6#2;

  label_7_true#2:
    assume _v2.INT_EQ(_v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v2.__ctobpl_const_35, se);
    assume _v2.value_is(_v2.__ctobpl_const_36, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_37, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)]);
    goto label_8#2;

  label_8#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 54} true;
    assume _v2.INT_GEQ(se, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        1))
     == 1;
    assert true;
    $encode_ie.arg.4$3.$$static$ := _v2.INT_PLUS(_v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    1)], 
  1, 
  2);
    assume _v2.value_is(_v2.__ctobpl_const_38, $encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_39, se);
    assume _v2.value_is(_v2.__ctobpl_const_40, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_41, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    1)]);
    goto label_9#2;

  label_9#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 53} true;
    assume _v2.INT_GEQ(se, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(se, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    call result.encode_ie$2 := _v2.encode_ie(buf, 6, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], $encode_ie.arg.4$3.$$static$, rsn_leader, 1);
    assume _v2.value_is(_v2.__ctobpl_const_42, se);
    assume _v2.value_is(_v2.__ctobpl_const_43, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_44, $encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_45, se);
    assume _v2.value_is(_v2.__ctobpl_const_46, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_47, $encode_ie.arg.4$3.$$static$);
    goto label_6#2;

  label_6#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 58} true;
    result.giwscan_cb$1 := 0;
    goto label_1#2;

  label_1#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 59} true;
    call _v2.__HAVOC_free(buf);
    call _v2.__HAVOC_free(rsn_leader);
    return;
}



implementation _v2.main() returns (result.main$1: int)
{
  var {:extern} havoc_stringTemp: int;
  var {:extern} condVal: int;
  var {:extern} ie: int;
  var {:extern} result.giwscan_cb$2: int;
  var {:extern} se: int;
  var {:extern} tempBoogie0: int;
  var {:extern} tempBoogie1: int;
  var {:extern} tempBoogie2: int;
  var {:extern} tempBoogie3: int;
  var {:extern} tempBoogie4: int;
  var {:extern} tempBoogie5: int;
  var {:extern} tempBoogie6: int;
  var {:extern} tempBoogie7: int;
  var {:extern} tempBoogie8: int;
  var {:extern} tempBoogie9: int;
  var {:extern} tempBoogie10: int;
  var {:extern} tempBoogie11: int;
  var {:extern} tempBoogie12: int;
  var {:extern} tempBoogie13: int;
  var {:extern} tempBoogie14: int;
  var {:extern} tempBoogie15: int;
  var {:extern} tempBoogie16: int;
  var {:extern} tempBoogie17: int;
  var {:extern} tempBoogie18: int;
  var {:extern} tempBoogie19: int;
  var {:extern} __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    call ie := _v2.__HAVOC_det_malloc(5);
    result.giwscan_cb$2 := 0;
    result.main$1 := 0;
    call se := _v2.__HAVOC_det_malloc(4);
    goto label_3#2;

  label_3#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 63} true;
    goto label_4#2;

  label_4#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 64} true;
    goto label_5#2;

  label_5#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 65} true;
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry := _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se) := ie];
    assume _v2.value_is(_v2.__ctobpl_const_48, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    goto label_6#2;

  label_6#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 66} true;
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        0))
     == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  1, 
  0) := 200];
    assume _v2.value_is(_v2.__ctobpl_const_49, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_50, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)]);
    goto label_7#2;

  label_7#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 67} true;
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        1))
     == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  1, 
  1) := 3];
    assume _v2.value_is(_v2.__ctobpl_const_51, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v2.__ctobpl_const_52, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    1)]);
    goto label_8#2;

  label_8#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 69} true;
    assume _v2.INT_GT(se, 0);
    assume _v2.INT_GT(se, 0);
    call result.giwscan_cb$2 := _v2.giwscan_cb(se);
    goto label_11#2;

  label_11#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 71} true;
    result.main$1 := 0;
    goto label_1#2;

  label_1#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 72} true;
    call _v2.__HAVOC_free(ie);
    call _v2.__HAVOC_free(se);
    return;
}



implementation _v2.encode_ie_loop_label_14_head(in_bufsize: int, in_i: int, in_ielen: int, in_p: int, in_tempBoogie0: int)
   returns (out_bufsize: int, out_i: int, out_p: int, out_tempBoogie0: int)
{

  entry#2:
    out_bufsize, out_i, out_p, out_tempBoogie0 := in_bufsize, in_i, in_p, in_tempBoogie0;
    goto label_14_head#2;

  label_14_head#2:
    goto label_14_true#2, label_14_false#2;

  label_14_false#2:
    assume !_v2.INT_LT(out_i, in_ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, out_i);
    assume _v2.value_is(_v2.__ctobpl_const_17, in_ielen);
    out_bufsize, out_i, out_p, out_tempBoogie0 := in_bufsize, in_i, in_p, in_tempBoogie0;
    _v2.Mem_T.UCHAR := old(_v2.Mem_T.UCHAR);
    return;

  label_14_true#2:
    assume _v2.INT_LT(out_i, in_ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, out_i);
    assume _v2.value_is(_v2.__ctobpl_const_17, in_ielen);
    goto label_16#2;

  label_16#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    goto label_16_true#2, label_16_false#2;

  label_16_false#2:
    assume !_v2.INT_LT(2, out_bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, out_bufsize);
    out_bufsize, out_i, out_p, out_tempBoogie0 := in_bufsize, in_i, in_p, in_tempBoogie0;
    _v2.Mem_T.UCHAR := old(_v2.Mem_T.UCHAR);
    return;

  label_16_true#2:
    assume _v2.INT_LT(2, out_bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, out_bufsize);
    goto label_17#2;

  label_17#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(out_p, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(out_p) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[out_p := 120];
    assume _v2.value_is(_v2.__ctobpl_const_21, out_p);
    assume _v2.value_is(_v2.__ctobpl_const_22, _v2.Mem_T.UCHAR[out_p]);
    goto label_18#2;

  label_18#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(out_p, 1, 1), 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(_v2.INT_PLUS(out_p, 1, 1)) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(out_p, 1, 1) := 120];
    assume _v2.value_is(_v2.__ctobpl_const_23, out_p);
    assume _v2.value_is(_v2.__ctobpl_const_24, _v2.Mem_T.UCHAR[_v2.INT_PLUS(out_p, 1, 1)]);
    goto label_19#2;

  label_19#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 33} true;
    out_tempBoogie0 := _v2.INT_PLUS(out_p, 1, 2);
    out_p := out_tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_25, out_p);
    goto label_20#2;

  label_20#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 34} true;
    havoc out_tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(out_bufsize, 2, 1, out_tempBoogie0);
    out_bufsize := out_tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_26, out_bufsize);
    goto label_21#2;

  label_21#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    assume _v2.value_is(_v2.__ctobpl_const_27, out_i);
    out_i := _v2.INT_PLUS(out_i, 1, 1);
    goto label_21_dummy#2;

  label_21_dummy#2:
    call out_bufsize, out_i, out_p, out_tempBoogie0 := _v2.encode_ie_loop_label_14_head(out_bufsize, out_i, in_ielen, out_p, out_tempBoogie0);
    return;
}



function _v1.ite(b: bool, x: int, y: int) : int;


var _v1.OK: bool;

var {:extern} _v1.Mem: [name][int]int;

var {:extern} _v1.alloc: int;

var {:extern} _v1.Mem_T.A1CHAR: [int]int;

var {:extern} _v1.Mem_T.A5UCHAR: [int]int;

var {:extern} _v1.Mem_T.A6UCHAR: [int]int;

var {:extern} _v1.Mem_T.CHAR: [int]int;

var {:extern} _v1.Mem_T.INT4: [int]int;

var {:extern} _v1.Mem_T.PCHAR: [int]int;

var {:extern} _v1.Mem_T.PUCHAR: [int]int;

var {:extern} _v1.Mem_T.PVOID: [int]int;

var {:extern} _v1.Mem_T.Pieee80211_scan_entry: [int]int;

var {:extern} _v1.Mem_T.UCHAR: [int]int;

var {:extern} _v1.Mem_T.VOID: [int]int;

var {:extern} _v1.Mem_T.ieee80211_scan_entry: [int]int;

var {:extern} _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;

var {:extern} _v1.detChoiceCnt: int;

var {:extern} _v1.Res_KERNEL_SOURCE: [int]int;

var {:extern} _v1.Res_PROBED: [int]int;

const {:extern} unique _v1.T.se_rsn_ie_ieee80211_scan_entry: name;

const {:extern} unique _v1.T.A1CHAR: name;

const {:extern} unique _v1.T.A5UCHAR: name;

const {:extern} unique _v1.T.A6UCHAR: name;

const {:extern} unique _v1.T.CHAR: name;

const {:extern} unique _v1.T.INT4: name;

const {:extern} unique _v1.T.PA1CHAR: name;

const {:extern} unique _v1.T.PA5UCHAR: name;

const {:extern} unique _v1.T.PA6UCHAR: name;

const {:extern} unique _v1.T.PCHAR: name;

const {:extern} unique _v1.T.PINT4: name;

const {:extern} unique _v1.T.PPCHAR: name;

const {:extern} unique _v1.T.PPUCHAR: name;

const {:extern} unique _v1.T.PPVOID: name;

const {:extern} unique _v1.T.PPieee80211_scan_entry: name;

const {:extern} unique _v1.T.PUCHAR: name;

const {:extern} unique _v1.T.PUINT4: name;

const {:extern} unique _v1.T.PVOID: name;

const {:extern} unique _v1.T.Pieee80211_scan_entry: name;

const {:extern} unique _v1.T.UCHAR: name;

const {:extern} unique _v1.T.UINT4: name;

const {:extern} unique _v1.T.VOID: name;

const {:extern} unique _v1.T.ieee80211_scan_entry: name;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 16} unique _v1.__ctobpl_const_5: int;

const {:extern} {:model_const "leader"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 16} unique _v1.__ctobpl_const_6: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 16} unique _v1.__ctobpl_const_7: int;

const {:extern} {:model_const "leader"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 16} unique _v1.__ctobpl_const_9: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 13} unique _v1.__ctobpl_const_1: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 16} unique _v1.__ctobpl_const_8: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 16} unique _v1.__ctobpl_const_10: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 13} unique _v1.__ctobpl_const_2: int;

const {:extern} {:model_const "*(p + 1)"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 32} unique _v1.__ctobpl_const_24: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 33} unique _v1.__ctobpl_const_25: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 20} unique _v1.__ctobpl_const_26: int;

const {:extern} {:model_const "result.question.3"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_28: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 17} unique _v1.__ctobpl_const_11: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 32} unique _v1.__ctobpl_const_23: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 18} unique _v1.__ctobpl_const_13: int;

const {:extern} {:model_const "buf"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_30: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 50} unique _v1.__ctobpl_const_32: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 17} unique _v1.__ctobpl_const_12: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 50} unique _v1.__ctobpl_const_33: int;

const {:extern} {:model_const "bufsize"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 20} unique _v1.__ctobpl_const_20: int;

const {:extern} {:model_const "*p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 30} unique _v1.__ctobpl_const_22: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_18: int;

const {:extern} {:model_const "result.question.3"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_31: int;

const {:extern} {:model_const "ielen"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_19: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 20} unique _v1.__ctobpl_const_16: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 30} unique _v1.__ctobpl_const_21: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_29: int;

const {:extern} {:model_const "result.question.3"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 38} unique _v1.__ctobpl_const_27: int;

const {:extern} {:model_const "ielen"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 20} unique _v1.__ctobpl_const_17: int;

const {:extern} {:model_const "leader_len"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 18} unique _v1.__ctobpl_const_14: int;

const {:extern} {:model_const "i"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 20} unique _v1.__ctobpl_const_15: int;

const {:extern} {:model_const "p"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 15} unique _v1.__ctobpl_const_3: int;

const {:extern} {:model_const "buf"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 15} unique _v1.__ctobpl_const_4: int;

const {:extern} {:model_const "se.se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 66} unique _v1.__ctobpl_const_50: int;

const {:extern} {:model_const "(se.se_rsn_ie)[0]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 65} unique _v1.__ctobpl_const_49: int;

const {:extern} {:model_const "se.se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 65} unique _v1.__ctobpl_const_48: int;

const {:extern} {:model_const "(se.se_rsn_ie)[1]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 66} unique _v1.__ctobpl_const_51: int;

const {:extern} {:model_const "se.se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 64} unique _v1.__ctobpl_const_47: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 52} unique _v1.__ctobpl_const_41: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 52} unique _v1.__ctobpl_const_42: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 52} unique _v1.__ctobpl_const_45: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 51} unique _v1.__ctobpl_const_35: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 52} unique _v1.__ctobpl_const_44: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 51} unique _v1.__ctobpl_const_34: int;

const {:extern} {:model_const "(se->se_rsn_ie)[1]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 53} unique _v1.__ctobpl_const_40: int;

const {:extern} {:model_const "se"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 53} unique _v1.__ctobpl_const_38: int;

const {:extern} {:model_const "encode_ie.arg.4"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 52} unique _v1.__ctobpl_const_43: int;

const {:extern} {:model_const "encode_ie.arg.4"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 52} unique _v1.__ctobpl_const_46: int;

const {:extern} {:model_const "(se->se_rsn_ie)[0]"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 51} unique _v1.__ctobpl_const_36: int;

const {:extern} {:model_const "encode_ie.arg.4"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 53} unique _v1.__ctobpl_const_37: int;

const {:extern} {:model_const "se->se_rsn_ie"} {:sourceFile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceLine 53} unique _v1.__ctobpl_const_39: int;

function {:inline true} _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(a : int, b : int, size : int, result : int) : bool
{
  (size * result <= a - b) && (a - b < size * (result + 1))
}



procedure _v1.havoc_assert(i: int);
  /* free */ requires i != 0;
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.havoc_assume(i: int);
  /* free */ ensures i != 0;
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.__HAVOC_free(a: int);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.__HAVOC_malloc(obj_size: int) returns (new: int);
  /* free */ requires _v2.INT_GEQ(obj_size, 0);
  modifies _v1.alloc;
  /* free */ ensures new == old(_v1.alloc);
  /* free */ ensures _v2.INT_GT(_v1.alloc, _v2.INT_ADD(new, obj_size));
  /* free */ ensures _v2.Base(new) == new;
  /* free */ ensures _v2.INT_GEQ(new, 0);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.__HAVOC_det_malloc(obj_size: int) returns (new: int);
  /* free */ requires _v2.INT_GEQ(obj_size, 0);
  modifies _v1.alloc;
  /* free */ ensures new == old(_v1.alloc);
  /* free */ ensures _v2.INT_GT(_v1.alloc, _v2.INT_ADD(new, obj_size));
  /* free */ ensures _v2.Base(new) == new;
  /* free */ ensures _v1.alloc == _v2.NewAlloc(old(_v1.alloc), obj_size);
  /* free */ ensures _v2.INT_GEQ(new, 0);
  /* free */ ensures _v1.OK ==> old(_v1.OK);




procedure _v1.nondet_choice() returns (x: int);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.det_choice() returns (x: int);
  modifies _v1.detChoiceCnt;
  /* free */ ensures _v1.detChoiceCnt == _v2.INT_ADD(old(_v1.detChoiceCnt), 1);
  /* free */ ensures x == _v2.DetChoiceFunc(old(_v1.detChoiceCnt));
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1._strdup(str: int) returns (new: int);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1._xstrcasecmp(a0: int, a1: int) returns (ret: int);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1._xstrcmp(a0: int, a1: int) returns (ret: int);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.memcpy(a0: int, a1: int, a2: int) returns (ret: int);
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.encode_ie(buf_.1: int, 
    bufsize_.1: int, 
    ie_.1: int, 
    ielen_.1: int, 
    leader_.1: int, 
    leader_len_.1: int)
   returns (result.encode_ie$1: int);
  modifies _v1.OK, _v1.Mem_T.UCHAR;
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.giwscan_cb(se_.1: int) returns (result.giwscan_cb$1: int);
  modifies _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.main() returns (result.main$1: int);
  modifies _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
  /* free */ ensures _v1.OK ==> old(_v1.OK);



procedure _v1.encode_ie_loop_label_14_head(in_bufsize: int, in_i: int, in_ielen: int, in_p: int, in_tempBoogie0: int)
   returns (out_i: int, out_p: int, out_tempBoogie0: int);
  modifies _v1.Mem_T.UCHAR, _v1.OK;
  /* free */ ensures _v1.OK ==> old(_v1.OK);



implementation _v1.encode_ie(buf_.1: int, 
    bufsize_.1: int, 
    ie_.1: int, 
    ielen_.1: int, 
    leader_.1: int, 
    leader_len_.1: int)
   returns (result.encode_ie$1: int)
{
  var {:extern} havoc_stringTemp: int;
  var {:extern} condVal: int;
  var {:extern} buf: int;
  var {:extern} bufsize: int;
  var {:extern} i: int;
  var {:extern} ie: int;
  var {:extern} ielen: int;
  var {:extern} leader: int;
  var {:extern} leader_len: int;
  var {:extern} p: int;
  var {:extern} result.memcpy$2: int;
  var {:extern} $result.question.3.$$static$: int;
  var {:extern} tempBoogie0: int;
  var {:extern} tempBoogie1: int;
  var {:extern} tempBoogie2: int;
  var {:extern} tempBoogie3: int;
  var {:extern} tempBoogie4: int;
  var {:extern} tempBoogie5: int;
  var {:extern} tempBoogie6: int;
  var {:extern} tempBoogie7: int;
  var {:extern} tempBoogie8: int;
  var {:extern} tempBoogie9: int;
  var {:extern} tempBoogie10: int;
  var {:extern} tempBoogie11: int;
  var {:extern} tempBoogie12: int;
  var {:extern} tempBoogie13: int;
  var {:extern} tempBoogie14: int;
  var {:extern} tempBoogie15: int;
  var {:extern} tempBoogie16: int;
  var {:extern} tempBoogie17: int;
  var {:extern} tempBoogie18: int;
  var {:extern} tempBoogie19: int;
  var {:extern} __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume _v2.INT_LT(buf_.1, _v1.alloc);
    assume _v2.INT_LT(ie_.1, _v1.alloc);
    assume _v2.INT_LT(leader_.1, _v1.alloc);
    buf := 0;
    assume _v2.INT_GEQ(buf_.1, 0);
    bufsize := 0;
    i := 0;
    ie := 0;
    assume _v2.INT_GEQ(ie_.1, 0);
    ielen := 0;
    leader := 0;
    assume _v2.INT_GEQ(leader_.1, 0);
    leader_len := 0;
    p := 0;
    result.encode_ie$1 := 0;
    result.memcpy$2 := 0;
    $result.question.3.$$static$ := 0;
    buf := buf_.1;
    bufsize := bufsize_.1;
    ie := ie_.1;
    ielen := ielen_.1;
    leader := leader_.1;
    leader_len := leader_len_.1;
    goto label_3#2;

  label_3#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 9} true;
    goto label_4#2;

  label_4#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 10} true;
    goto label_5#2;

  label_5#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 13} true;
    goto label_5_true#2, label_5_false#2;

  label_5_false#2:
    assume !_v2.INT_LT(bufsize, leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_1, bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_2, leader_len);
    goto label_6#2;

  label_6#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 15} true;
    p := buf;
    assume _v2.value_is(_v1.__ctobpl_const_3, p);
    assume _v2.value_is(_v1.__ctobpl_const_4, buf);
    goto label_8#2;

  label_8#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 16} true;
    call result.memcpy$2 := _v1.memcpy(p, leader, leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_5, p);
    assume _v2.value_is(_v1.__ctobpl_const_6, leader);
    assume _v2.value_is(_v1.__ctobpl_const_7, leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_8, p);
    assume _v2.value_is(_v1.__ctobpl_const_9, leader);
    assume _v2.value_is(_v1.__ctobpl_const_10, leader_len);
    goto label_11#2;

  label_11#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 17} true;
    havoc tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(bufsize, leader_len, 1, tempBoogie0);
    bufsize := tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_11, bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_12, leader_len);
    goto label_12#2;

  label_12#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 18} true;
    tempBoogie0 := _v2.INT_PLUS(p, 1, leader_len);
    p := tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_13, p);
    assume _v2.value_is(_v1.__ctobpl_const_14, leader_len);
    goto label_13#2;

  label_13#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    i := 0;
    assume _v2.value_is(_v1.__ctobpl_const_15, i);
    goto label_14#2;

  label_14#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    goto label_14_head#2;

  label_14_head#2:
    call i, p, tempBoogie0 := _v1.encode_ie_loop_label_14_head(bufsize, i, ielen, p, tempBoogie0);
    goto label_14_head_last#2;

  label_14_head_last#2:
    goto label_14_true#2, label_14_false#2;

  label_14_false#2:
    assume !_v2.INT_LT(i, ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, i);
    assume _v2.value_is(_v1.__ctobpl_const_17, ielen);
    goto label_15#2;

  label_14_true#2:
    assume _v2.INT_LT(i, ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, i);
    assume _v2.value_is(_v1.__ctobpl_const_17, ielen);
    goto label_16#2;

  label_16#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    goto label_16_true#2, label_16_false#2;

  label_16_false#2:
    assume !_v2.INT_LT(2, bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, bufsize);
    goto label_15#2;

  label_15#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    goto label_15_true#2, label_15_false#2;

  label_15_false#2:
    assume !_v2.INT_EQ(i, ielen);
    assume _v2.value_is(_v1.__ctobpl_const_18, i);
    assume _v2.value_is(_v1.__ctobpl_const_19, ielen);
    goto label_21#2;

  label_21#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    $result.question.3.$$static$ := 0;
    assume _v2.value_is(_v1.__ctobpl_const_27, $result.question.3.$$static$);
    goto label_23#2;

  label_15_true#2:
    assume _v2.INT_EQ(i, ielen);
    assume _v2.value_is(_v1.__ctobpl_const_18, i);
    assume _v2.value_is(_v1.__ctobpl_const_19, ielen);
    goto label_22#2;

  label_22#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    havoc $result.question.3.$$static$;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(p, buf, 1, $result.question.3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_28, $result.question.3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_29, p);
    assume _v2.value_is(_v1.__ctobpl_const_30, buf);
    goto label_23#2;

  label_23#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    result.encode_ie$1 := $result.question.3.$$static$;
    assume _v2.value_is(_v1.__ctobpl_const_31, $result.question.3.$$static$);
    goto label_1#2;

  label_16_true#2:
    assume _v2.INT_LT(2, bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, bufsize);
    goto label_17#2;

  label_17#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(p, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(p) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[p := 120];
    assume _v2.value_is(_v1.__ctobpl_const_21, p);
    assume _v2.value_is(_v1.__ctobpl_const_22, _v1.Mem_T.UCHAR[p]);
    goto label_18#2;

  label_18#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(p, 1, 1), 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.INT_PLUS(p, 1, 1)) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(p, 1, 1) := 120];
    assume _v2.value_is(_v1.__ctobpl_const_23, p);
    assume _v2.value_is(_v1.__ctobpl_const_24, _v1.Mem_T.UCHAR[_v2.INT_PLUS(p, 1, 1)]);
    goto label_19#2;

  label_19#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 33} true;
    tempBoogie0 := _v2.INT_PLUS(p, 1, 2);
    p := tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_25, p);
    goto label_20#2;

  label_20#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    assume _v2.value_is(_v1.__ctobpl_const_26, i);
    i := _v2.INT_PLUS(i, 1, 1);
    goto label_20_dummy#2;

  label_20_dummy#2:
    assume false;
    return;

  label_5_true#2:
    assume _v2.INT_LT(bufsize, leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_1, bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_2, leader_len);
    goto label_7#2;

  label_7#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 14} true;
    result.encode_ie$1 := 0;
    goto label_1#2;

  label_1#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 39} true;
    return;
}



implementation _v1.giwscan_cb(se_.1: int) returns (result.giwscan_cb$1: int)
{
  var {:extern} havoc_stringTemp: int;
  var {:extern} condVal: int;
  var {:extern} buf: int;
  var {:extern} $encode_ie.arg.4$3.$$static$: int;
  var {:extern} result.encode_ie$2: int;
  var {:extern} rsn_leader: int;
  var {:extern} se: int;
  var {:extern} tempBoogie0: int;
  var {:extern} tempBoogie1: int;
  var {:extern} tempBoogie2: int;
  var {:extern} tempBoogie3: int;
  var {:extern} tempBoogie4: int;
  var {:extern} tempBoogie5: int;
  var {:extern} tempBoogie6: int;
  var {:extern} tempBoogie7: int;
  var {:extern} tempBoogie8: int;
  var {:extern} tempBoogie9: int;
  var {:extern} tempBoogie10: int;
  var {:extern} tempBoogie11: int;
  var {:extern} tempBoogie12: int;
  var {:extern} tempBoogie13: int;
  var {:extern} tempBoogie14: int;
  var {:extern} tempBoogie15: int;
  var {:extern} tempBoogie16: int;
  var {:extern} tempBoogie17: int;
  var {:extern} tempBoogie18: int;
  var {:extern} tempBoogie19: int;
  var {:extern} __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    assume _v2.INT_LT(se_.1, _v1.alloc);
    call buf := _v1.__HAVOC_det_malloc(6);
    $encode_ie.arg.4$3.$$static$ := 0;
    result.encode_ie$2 := 0;
    result.giwscan_cb$1 := 0;
    call rsn_leader := _v1.__HAVOC_det_malloc(1);
    se := 0;
    assume _v2.INT_GEQ(se_.1, 0);
    se := se_.1;
    goto label_3#2;

  label_3#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 45} true;
    goto label_4#2;

  label_4#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 46} true;
    goto label_5#2;

  label_5#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 50} true;
    assume _v2.INT_GEQ(se, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    goto label_5_true#2, label_5_false#2;

  label_5_false#2:
    assume _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]
   == 0;
    assume _v2.value_is(_v1.__ctobpl_const_32, se);
    assume _v2.value_is(_v1.__ctobpl_const_33, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    goto label_6#2;

  label_5_true#2:
    assume _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]
   != 0;
    assume _v2.value_is(_v1.__ctobpl_const_32, se);
    assume _v2.value_is(_v1.__ctobpl_const_33, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    goto label_7#2;

  label_7#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 51} true;
    assume _v2.INT_GEQ(se, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        0))
     == 1;
    assert true;
    goto label_7_true#2, label_7_false#2;

  label_7_false#2:
    assume !_v2.INT_EQ(_v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v1.__ctobpl_const_34, se);
    assume _v2.value_is(_v1.__ctobpl_const_35, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_36, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)]);
    goto label_6#2;

  label_7_true#2:
    assume _v2.INT_EQ(_v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v1.__ctobpl_const_34, se);
    assume _v2.value_is(_v1.__ctobpl_const_35, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_36, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)]);
    goto label_8#2;

  label_8#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 53} true;
    assume _v2.INT_GEQ(se, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        1))
     == 1;
    assert true;
    $encode_ie.arg.4$3.$$static$ := _v2.INT_PLUS(_v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    1)], 
  1, 
  2);
    assume _v2.value_is(_v1.__ctobpl_const_37, $encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_38, se);
    assume _v2.value_is(_v1.__ctobpl_const_39, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_40, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    1)]);
    goto label_9#2;

  label_9#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 52} true;
    assume _v2.INT_GEQ(se, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(se, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    call result.encode_ie$2 := _v1.encode_ie(buf, 6, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], $encode_ie.arg.4$3.$$static$, rsn_leader, 1);
    assume _v2.value_is(_v1.__ctobpl_const_41, se);
    assume _v2.value_is(_v1.__ctobpl_const_42, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_43, $encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_44, se);
    assume _v2.value_is(_v1.__ctobpl_const_45, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_46, $encode_ie.arg.4$3.$$static$);
    goto label_6#2;

  label_6#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 57} true;
    result.giwscan_cb$1 := 0;
    goto label_1#2;

  label_1#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 58} true;
    call _v1.__HAVOC_free(buf);
    call _v1.__HAVOC_free(rsn_leader);
    return;
}



implementation _v1.main() returns (result.main$1: int)
{
  var {:extern} havoc_stringTemp: int;
  var {:extern} condVal: int;
  var {:extern} ie: int;
  var {:extern} result.giwscan_cb$2: int;
  var {:extern} se: int;
  var {:extern} tempBoogie0: int;
  var {:extern} tempBoogie1: int;
  var {:extern} tempBoogie2: int;
  var {:extern} tempBoogie3: int;
  var {:extern} tempBoogie4: int;
  var {:extern} tempBoogie5: int;
  var {:extern} tempBoogie6: int;
  var {:extern} tempBoogie7: int;
  var {:extern} tempBoogie8: int;
  var {:extern} tempBoogie9: int;
  var {:extern} tempBoogie10: int;
  var {:extern} tempBoogie11: int;
  var {:extern} tempBoogie12: int;
  var {:extern} tempBoogie13: int;
  var {:extern} tempBoogie14: int;
  var {:extern} tempBoogie15: int;
  var {:extern} tempBoogie16: int;
  var {:extern} tempBoogie17: int;
  var {:extern} tempBoogie18: int;
  var {:extern} tempBoogie19: int;
  var {:extern} __havoc_dummy_return: int;

  anon0#2:
    havoc_stringTemp := 0;
    goto start#2;

  start#2:
    call ie := _v1.__HAVOC_det_malloc(5);
    result.giwscan_cb$2 := 0;
    result.main$1 := 0;
    call se := _v1.__HAVOC_det_malloc(4);
    goto label_3#2;

  label_3#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 62} true;
    goto label_4#2;

  label_4#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 63} true;
    goto label_5#2;

  label_5#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 64} true;
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry := _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se) := ie];
    assume _v2.value_is(_v1.__ctobpl_const_47, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    goto label_6#2;

  label_6#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 65} true;
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        0))
     == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  1, 
  0) := 200];
    assume _v2.value_is(_v1.__ctobpl_const_48, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_49, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    0)]);
    goto label_7#2;

  label_7#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 66} true;
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(se)) == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
        1, 
        1))
     == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
  1, 
  1) := 3];
    assume _v2.value_is(_v1.__ctobpl_const_50, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)]);
    assume _v2.value_is(_v1.__ctobpl_const_51, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(se)], 
    1, 
    1)]);
    goto label_8#2;

  label_8#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 68} true;
    assume _v2.INT_GT(se, 0);
    assume _v2.INT_GT(se, 0);
    call result.giwscan_cb$2 := _v1.giwscan_cb(se);
    goto label_11#2;

  label_11#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 70} true;
    result.main$1 := 0;
    goto label_1#2;

  label_1#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 71} true;
    call _v1.__HAVOC_free(ie);
    call _v1.__HAVOC_free(se);
    return;
}



implementation _v1.encode_ie_loop_label_14_head(in_bufsize: int, in_i: int, in_ielen: int, in_p: int, in_tempBoogie0: int)
   returns (out_i: int, out_p: int, out_tempBoogie0: int)
{

  entry#2:
    out_i, out_p, out_tempBoogie0 := in_i, in_p, in_tempBoogie0;
    goto label_14_head#2;

  label_14_head#2:
    goto label_14_true#2, label_14_false#2;

  label_14_false#2:
    assume !_v2.INT_LT(out_i, in_ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, out_i);
    assume _v2.value_is(_v1.__ctobpl_const_17, in_ielen);
    out_i, out_p, out_tempBoogie0 := in_i, in_p, in_tempBoogie0;
    _v1.Mem_T.UCHAR := old(_v1.Mem_T.UCHAR);
    return;

  label_14_true#2:
    assume _v2.INT_LT(out_i, in_ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, out_i);
    assume _v2.value_is(_v1.__ctobpl_const_17, in_ielen);
    goto label_16#2;

  label_16#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    goto label_16_true#2, label_16_false#2;

  label_16_false#2:
    assume !_v2.INT_LT(2, in_bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, in_bufsize);
    out_i, out_p, out_tempBoogie0 := in_i, in_p, in_tempBoogie0;
    _v1.Mem_T.UCHAR := old(_v1.Mem_T.UCHAR);
    return;

  label_16_true#2:
    assume _v2.INT_LT(2, in_bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, in_bufsize);
    goto label_17#2;

  label_17#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(out_p, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(out_p) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[out_p := 120];
    assume _v2.value_is(_v1.__ctobpl_const_21, out_p);
    assume _v2.value_is(_v1.__ctobpl_const_22, _v1.Mem_T.UCHAR[out_p]);
    goto label_18#2;

  label_18#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(out_p, 1, 1), 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(_v2.INT_PLUS(out_p, 1, 1)) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(out_p, 1, 1) := 120];
    assume _v2.value_is(_v1.__ctobpl_const_23, out_p);
    assume _v2.value_is(_v1.__ctobpl_const_24, _v1.Mem_T.UCHAR[_v2.INT_PLUS(out_p, 1, 1)]);
    goto label_19#2;

  label_19#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 33} true;
    out_tempBoogie0 := _v2.INT_PLUS(out_p, 1, 2);
    out_p := out_tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_25, out_p);
    goto label_20#2;

  label_20#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    assume _v2.value_is(_v1.__ctobpl_const_26, out_i);
    out_i := _v2.INT_PLUS(out_i, 1, 1);
    goto label_20_dummy#2;

  label_20_dummy#2:
    call out_i, out_p, out_tempBoogie0 := _v1.encode_ie_loop_label_14_head(in_bufsize, out_i, in_ielen, out_p, out_tempBoogie0);
    return;
}



type {:extern} name;

type {:extern} byte;

function {:inline true} MS$_v1.havoc_assert$_v2.havoc_assert(_v1.i: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v2.i: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int)
   : bool
{
  true
}

procedure MS_Check__v1.havoc_assert___v2.havoc_assert(_v1.i: int, _v2.i: int);
  requires _v1.i == _v2.i
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.havoc_assert$_v2.havoc_assert(_v1.i, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v2.i, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED));
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.havoc_assume$_v2.havoc_assume(_v1.i: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v2.i: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int)
   : bool
{
  true
}

procedure MS_Check__v1.havoc_assume___v2.havoc_assume(_v1.i: int, _v2.i: int);
  requires _v1.i == _v2.i
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.havoc_assume$_v2.havoc_assume(_v1.i, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v2.i, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED));
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.__HAVOC_free$_v2.__HAVOC_free(_v1.a: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v2.a: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int)
   : bool
{
  true
}

const {:existential true} _houdini_0: bool;

const {:existential true} _houdini_1: bool;

const {:existential true} _houdini_2: bool;

const {:existential true} _houdini_3: bool;

const {:existential true} _houdini_4: bool;

const {:existential true} _houdini_5: bool;

const {:existential true} _houdini_6: bool;

const {:existential true} _houdini_7: bool;

const {:existential true} _houdini_8: bool;

const {:existential true} _houdini_9: bool;

const {:existential true} _houdini_10: bool;

const {:existential true} _houdini_11: bool;

const {:existential true} _houdini_12: bool;

const {:existential true} _houdini_13: bool;

const {:existential true} _houdini_14: bool;

const {:existential true} _houdini_15: bool;

const {:existential true} _houdini_16: bool;

const {:existential true} _houdini_17: bool;

const {:existential true} _houdini_18: bool;

const {:existential true} _houdini_19: bool;

const {:existential true} _houdini_20: bool;

const {:existential true} _houdini_21: bool;

const {:existential true} _houdini_22: bool;

const {:existential true} _houdini_23: bool;

procedure MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.a: int, _v2.a: int);
  requires _houdini_0 ==> _v1.a <= _v2.a;
  requires _houdini_1 ==> _v2.a <= _v1.a;
  requires _houdini_2 ==> _v1.OK ==> _v2.OK;
  requires _houdini_3 ==> _v2.OK ==> _v1.OK;
  requires _houdini_4 ==> _v1.Mem == _v2.Mem;
  requires _houdini_5 ==> _v1.alloc <= _v2.alloc;
  requires _houdini_6 ==> _v2.alloc <= _v1.alloc;
  requires _houdini_7 ==> _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR;
  requires _houdini_8 ==> _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR;
  requires _houdini_9 ==> _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR;
  requires _houdini_10 ==> _v1.Mem_T.CHAR == _v2.Mem_T.CHAR;
  requires _houdini_11 ==> _v1.Mem_T.INT4 == _v2.Mem_T.INT4;
  requires _houdini_12 ==> _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR;
  requires _houdini_13 ==> _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR;
  requires _houdini_14 ==> _v1.Mem_T.PVOID == _v2.Mem_T.PVOID;
  requires _houdini_15
   ==> _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry;
  requires _houdini_16 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  requires _houdini_17 ==> _v1.Mem_T.VOID == _v2.Mem_T.VOID;
  requires _houdini_18 ==> _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry;
  requires _houdini_19
   ==> _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
  requires _houdini_20 ==> _v1.detChoiceCnt <= _v2.detChoiceCnt;
  requires _houdini_21 ==> _v2.detChoiceCnt <= _v1.detChoiceCnt;
  requires _houdini_22 ==> _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE;
  requires _houdini_23 ==> _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.__HAVOC_free$_v2.__HAVOC_free(_v1.a, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v2.a, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED));
  ensures old(_v1.a == _v2.a) ==> true;



function {:inline true} MS$_v1.__HAVOC_malloc$_v2.__HAVOC_malloc(_v1.obj_size: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.alloc_: int, 
    _v1.new: int, 
    _v2.obj_size: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.alloc_: int, 
    _v2.new: int)
   : bool
{
  true
}

procedure MS_Check__v1.__HAVOC_malloc___v2.__HAVOC_malloc(_v1.obj_size: int, _v2.obj_size: int) returns (_v1.new: int, _v2.new: int);
  requires _v1.obj_size == _v2.obj_size
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.alloc, _v2.alloc;
  ensures MS$_v1.__HAVOC_malloc$_v2.__HAVOC_malloc(_v1.obj_size, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.alloc, 
  _v1.new, 
  _v2.obj_size, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.alloc, 
  _v2.new);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.__HAVOC_det_malloc$_v2.__HAVOC_det_malloc(_v1.obj_size: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.alloc_: int, 
    _v1.new: int, 
    _v2.obj_size: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.alloc_: int, 
    _v2.new: int)
   : bool
{
  true
}

const {:existential true} _houdini_24: bool;

const {:existential true} _houdini_25: bool;

const {:existential true} _houdini_26: bool;

const {:existential true} _houdini_27: bool;

const {:existential true} _houdini_28: bool;

const {:existential true} _houdini_29: bool;

const {:existential true} _houdini_30: bool;

const {:existential true} _houdini_31: bool;

const {:existential true} _houdini_32: bool;

const {:existential true} _houdini_33: bool;

const {:existential true} _houdini_34: bool;

const {:existential true} _houdini_35: bool;

const {:existential true} _houdini_36: bool;

const {:existential true} _houdini_37: bool;

const {:existential true} _houdini_38: bool;

const {:existential true} _houdini_39: bool;

const {:existential true} _houdini_40: bool;

const {:existential true} _houdini_41: bool;

const {:existential true} _houdini_42: bool;

const {:existential true} _houdini_43: bool;

const {:existential true} _houdini_44: bool;

const {:existential true} _houdini_45: bool;

const {:existential true} _houdini_46: bool;

const {:existential true} _houdini_47: bool;

procedure MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.obj_size: int, _v2.obj_size: int) returns (_v1.new: int, _v2.new: int);
  requires _houdini_24 ==> _v1.obj_size <= _v2.obj_size;
  requires _houdini_25 ==> _v2.obj_size <= _v1.obj_size;
  requires _houdini_26 ==> _v1.OK ==> _v2.OK;
  requires _houdini_27 ==> _v2.OK ==> _v1.OK;
  requires _houdini_28 ==> _v1.Mem == _v2.Mem;
  requires _houdini_29 ==> _v1.alloc <= _v2.alloc;
  requires _houdini_30 ==> _v2.alloc <= _v1.alloc;
  requires _houdini_31 ==> _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR;
  requires _houdini_32 ==> _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR;
  requires _houdini_33 ==> _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR;
  requires _houdini_34 ==> _v1.Mem_T.CHAR == _v2.Mem_T.CHAR;
  requires _houdini_35 ==> _v1.Mem_T.INT4 == _v2.Mem_T.INT4;
  requires _houdini_36 ==> _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR;
  requires _houdini_37 ==> _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR;
  requires _houdini_38 ==> _v1.Mem_T.PVOID == _v2.Mem_T.PVOID;
  requires _houdini_39
   ==> _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry;
  requires _houdini_40 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  requires _houdini_41 ==> _v1.Mem_T.VOID == _v2.Mem_T.VOID;
  requires _houdini_42 ==> _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry;
  requires _houdini_43
   ==> _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
  requires _houdini_44 ==> _v1.detChoiceCnt <= _v2.detChoiceCnt;
  requires _houdini_45 ==> _v2.detChoiceCnt <= _v1.detChoiceCnt;
  requires _houdini_46 ==> _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE;
  requires _houdini_47 ==> _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.alloc, _v2.alloc;
  ensures MS$_v1.__HAVOC_det_malloc$_v2.__HAVOC_det_malloc(_v1.obj_size, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.alloc, 
  _v1.new, 
  _v2.obj_size, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.alloc, 
  _v2.new);
  ensures old(_v1.obj_size == _v2.obj_size && _v1.alloc == _v2.alloc)
   ==> _v1.new <= _v2.new
     && _v2.new <= _v1.new
     && _v1.alloc <= _v2.alloc
     && _v2.alloc <= _v1.alloc;



function {:inline true} MS$_v1.__HAVOC_memset_split_1$_v2.__HAVOC_memset_split_1(_v1.A: [int]int, 
    _v1.p: int, 
    _v1.c: int, 
    _v1.n: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.ret: [int]int, 
    _v2.A: [int]int, 
    _v2.p: int, 
    _v2.c: int, 
    _v2.n: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.ret: [int]int)
   : bool
{
  true
}

procedure MS_Check__v1.__HAVOC_memset_split_1___v2.__HAVOC_memset_split_1(_v1.A: [int]int, 
    _v1.p: int, 
    _v1.c: int, 
    _v1.n: int, 
    _v2.A: [int]int, 
    _v2.p: int, 
    _v2.c: int, 
    _v2.n: int)
   returns (_v1.ret: [int]int, _v2.ret: [int]int);
  requires _v1.A == _v2.A
   && _v1.p == _v2.p
   && _v1.c == _v2.c
   && _v1.n == _v2.n
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.__HAVOC_memset_split_1$_v2.__HAVOC_memset_split_1(_v1.A, 
  _v1.p, 
  _v1.c, 
  _v1.n, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.ret, 
  _v2.A, 
  _v2.p, 
  _v2.c, 
  _v2.n, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.ret);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.__HAVOC_memset_split_2$_v2.__HAVOC_memset_split_2(_v1.A: [int]int, 
    _v1.p: int, 
    _v1.c: int, 
    _v1.n: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.ret: [int]int, 
    _v2.A: [int]int, 
    _v2.p: int, 
    _v2.c: int, 
    _v2.n: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.ret: [int]int)
   : bool
{
  true
}

procedure MS_Check__v1.__HAVOC_memset_split_2___v2.__HAVOC_memset_split_2(_v1.A: [int]int, 
    _v1.p: int, 
    _v1.c: int, 
    _v1.n: int, 
    _v2.A: [int]int, 
    _v2.p: int, 
    _v2.c: int, 
    _v2.n: int)
   returns (_v1.ret: [int]int, _v2.ret: [int]int);
  requires _v1.A == _v2.A
   && _v1.p == _v2.p
   && _v1.c == _v2.c
   && _v1.n == _v2.n
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.__HAVOC_memset_split_2$_v2.__HAVOC_memset_split_2(_v1.A, 
  _v1.p, 
  _v1.c, 
  _v1.n, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.ret, 
  _v2.A, 
  _v2.p, 
  _v2.c, 
  _v2.n, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.ret);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.__HAVOC_memset_split_4$_v2.__HAVOC_memset_split_4(_v1.A: [int]int, 
    _v1.p: int, 
    _v1.c: int, 
    _v1.n: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.ret: [int]int, 
    _v2.A: [int]int, 
    _v2.p: int, 
    _v2.c: int, 
    _v2.n: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.ret: [int]int)
   : bool
{
  true
}

procedure MS_Check__v1.__HAVOC_memset_split_4___v2.__HAVOC_memset_split_4(_v1.A: [int]int, 
    _v1.p: int, 
    _v1.c: int, 
    _v1.n: int, 
    _v2.A: [int]int, 
    _v2.p: int, 
    _v2.c: int, 
    _v2.n: int)
   returns (_v1.ret: [int]int, _v2.ret: [int]int);
  requires _v1.A == _v2.A
   && _v1.p == _v2.p
   && _v1.c == _v2.c
   && _v1.n == _v2.n
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.__HAVOC_memset_split_4$_v2.__HAVOC_memset_split_4(_v1.A, 
  _v1.p, 
  _v1.c, 
  _v1.n, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.ret, 
  _v2.A, 
  _v2.p, 
  _v2.c, 
  _v2.n, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.ret);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.nondet_choice$_v2.nondet_choice(_v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.x: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.x: int)
   : bool
{
  true
}

procedure MS_Check__v1.nondet_choice___v2.nondet_choice() returns (_v1.x: int, _v2.x: int);
  requires (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.nondet_choice$_v2.nondet_choice(old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.x, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.x);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.det_choice$_v2.det_choice(_v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.detChoiceCnt_: int, 
    _v1.x: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.detChoiceCnt_: int, 
    _v2.x: int)
   : bool
{
  true
}

procedure MS_Check__v1.det_choice___v2.det_choice() returns (_v1.x: int, _v2.x: int);
  requires (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.detChoiceCnt, _v2.detChoiceCnt;
  ensures MS$_v1.det_choice$_v2.det_choice(old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.detChoiceCnt, 
  _v1.x, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.detChoiceCnt, 
  _v2.x);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1._strdup$_v2._strdup(_v1.str: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.new: int, 
    _v2.str: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.new: int)
   : bool
{
  true
}

procedure MS_Check__v1._strdup___v2._strdup(_v1.str: int, _v2.str: int) returns (_v1.new: int, _v2.new: int);
  requires _v1.str == _v2.str
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1._strdup$_v2._strdup(_v1.str, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.new, 
  _v2.str, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.new);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1._xstrcasecmp$_v2._xstrcasecmp(_v1.a0: int, 
    _v1.a1: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.ret: int, 
    _v2.a0: int, 
    _v2.a1: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.ret: int)
   : bool
{
  true
}

procedure MS_Check__v1._xstrcasecmp___v2._xstrcasecmp(_v1.a0: int, _v1.a1: int, _v2.a0: int, _v2.a1: int)
   returns (_v1.ret: int, _v2.ret: int);
  requires _v1.a0 == _v2.a0
   && _v1.a1 == _v2.a1
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1._xstrcasecmp$_v2._xstrcasecmp(_v1.a0, 
  _v1.a1, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.ret, 
  _v2.a0, 
  _v2.a1, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.ret);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1._xstrcmp$_v2._xstrcmp(_v1.a0: int, 
    _v1.a1: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.ret: int, 
    _v2.a0: int, 
    _v2.a1: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.ret: int)
   : bool
{
  true
}

procedure MS_Check__v1._xstrcmp___v2._xstrcmp(_v1.a0: int, _v1.a1: int, _v2.a0: int, _v2.a1: int)
   returns (_v1.ret: int, _v2.ret: int);
  requires _v1.a0 == _v2.a0
   && _v1.a1 == _v2.a1
   && 
  (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1._xstrcmp$_v2._xstrcmp(_v1.a0, 
  _v1.a1, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.ret, 
  _v2.a0, 
  _v2.a1, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.ret);
  ensures _v1.OK ==> _v2.OK;



function {:inline true} MS$_v1.memcpy$_v2.memcpy(_v1.a0: int, 
    _v1.a1: int, 
    _v1.a2: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.ret: int, 
    _v2.a0: int, 
    _v2.a1: int, 
    _v2.a2: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.ret: int)
   : bool
{
  true
}

const {:existential true} _houdini_48: bool;

const {:existential true} _houdini_49: bool;

const {:existential true} _houdini_50: bool;

const {:existential true} _houdini_51: bool;

const {:existential true} _houdini_52: bool;

const {:existential true} _houdini_53: bool;

const {:existential true} _houdini_54: bool;

const {:existential true} _houdini_55: bool;

const {:existential true} _houdini_56: bool;

const {:existential true} _houdini_57: bool;

const {:existential true} _houdini_58: bool;

const {:existential true} _houdini_59: bool;

const {:existential true} _houdini_60: bool;

const {:existential true} _houdini_61: bool;

const {:existential true} _houdini_62: bool;

const {:existential true} _houdini_63: bool;

const {:existential true} _houdini_64: bool;

const {:existential true} _houdini_65: bool;

const {:existential true} _houdini_66: bool;

const {:existential true} _houdini_67: bool;

const {:existential true} _houdini_68: bool;

const {:existential true} _houdini_69: bool;

const {:existential true} _houdini_70: bool;

const {:existential true} _houdini_71: bool;

const {:existential true} _houdini_72: bool;

const {:existential true} _houdini_73: bool;

const {:existential true} _houdini_74: bool;

const {:existential true} _houdini_75: bool;

procedure MS_Check__v1.memcpy___v2.memcpy(_v1.a0: int, _v1.a1: int, _v1.a2: int, _v2.a0: int, _v2.a1: int, _v2.a2: int)
   returns (_v1.ret: int, _v2.ret: int);
  requires _houdini_48 ==> _v1.a0 <= _v2.a0;
  requires _houdini_49 ==> _v2.a0 <= _v1.a0;
  requires _houdini_50 ==> _v1.a1 <= _v2.a1;
  requires _houdini_51 ==> _v2.a1 <= _v1.a1;
  requires _houdini_52 ==> _v1.a2 <= _v2.a2;
  requires _houdini_53 ==> _v2.a2 <= _v1.a2;
  requires _houdini_54 ==> _v1.OK ==> _v2.OK;
  requires _houdini_55 ==> _v2.OK ==> _v1.OK;
  requires _houdini_56 ==> _v1.Mem == _v2.Mem;
  requires _houdini_57 ==> _v1.alloc <= _v2.alloc;
  requires _houdini_58 ==> _v2.alloc <= _v1.alloc;
  requires _houdini_59 ==> _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR;
  requires _houdini_60 ==> _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR;
  requires _houdini_61 ==> _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR;
  requires _houdini_62 ==> _v1.Mem_T.CHAR == _v2.Mem_T.CHAR;
  requires _houdini_63 ==> _v1.Mem_T.INT4 == _v2.Mem_T.INT4;
  requires _houdini_64 ==> _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR;
  requires _houdini_65 ==> _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR;
  requires _houdini_66 ==> _v1.Mem_T.PVOID == _v2.Mem_T.PVOID;
  requires _houdini_67
   ==> _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry;
  requires _houdini_68 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  requires _houdini_69 ==> _v1.Mem_T.VOID == _v2.Mem_T.VOID;
  requires _houdini_70 ==> _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry;
  requires _houdini_71
   ==> _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
  requires _houdini_72 ==> _v1.detChoiceCnt <= _v2.detChoiceCnt;
  requires _houdini_73 ==> _v2.detChoiceCnt <= _v1.detChoiceCnt;
  requires _houdini_74 ==> _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE;
  requires _houdini_75 ==> _v1.Res_PROBED == _v2.Res_PROBED;
  ensures MS$_v1.memcpy$_v2.memcpy(_v1.a0, 
  _v1.a1, 
  _v1.a2, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.ret, 
  _v2.a0, 
  _v2.a1, 
  _v2.a2, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.ret);
  ensures old(_v1.a0 == _v2.a0 && _v1.a1 == _v2.a1 && _v1.a2 == _v2.a2)
   ==> _v1.ret <= _v2.ret && _v2.ret <= _v1.ret;



function {:inline true} MS$_v1.encode_ie$_v2.encode_ie(_v1.buf_.1: int, 
    _v1.bufsize_.1: int, 
    _v1.ie_.1: int, 
    _v1.ielen_.1: int, 
    _v1.leader_.1: int, 
    _v1.leader_len_.1: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.OK_: bool, 
    _v1.Mem_T.UCHAR_: [int]int, 
    _v1.result.encode_ie$1: int, 
    _v2.buf_.1: int, 
    _v2.bufsize_.1: int, 
    _v2.ie_.1: int, 
    _v2.ielen_.1: int, 
    _v2.leader_.1: int, 
    _v2.leader_len_.1: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.OK_: bool, 
    _v2.Mem_T.UCHAR_: [int]int, 
    _v2.result.encode_ie$1: int)
   : bool
{
  true
}

const {:existential true} _houdini_76: bool;

const {:existential true} _houdini_77: bool;

const {:existential true} _houdini_78: bool;

const {:existential true} _houdini_79: bool;

const {:existential true} _houdini_80: bool;

const {:existential true} _houdini_81: bool;

const {:existential true} _houdini_82: bool;

const {:existential true} _houdini_83: bool;

const {:existential true} _houdini_84: bool;

const {:existential true} _houdini_85: bool;

const {:existential true} _houdini_86: bool;

const {:existential true} _houdini_87: bool;

const {:existential true} _houdini_88: bool;

const {:existential true} _houdini_89: bool;

const {:existential true} _houdini_90: bool;

const {:existential true} _houdini_91: bool;

const {:existential true} _houdini_92: bool;

const {:existential true} _houdini_93: bool;

const {:existential true} _houdini_94: bool;

const {:existential true} _houdini_95: bool;

const {:existential true} _houdini_96: bool;

const {:existential true} _houdini_97: bool;

const {:existential true} _houdini_98: bool;

const {:existential true} _houdini_99: bool;

const {:existential true} _houdini_100: bool;

const {:existential true} _houdini_101: bool;

const {:existential true} _houdini_102: bool;

const {:existential true} _houdini_103: bool;

const {:existential true} _houdini_104: bool;

const {:existential true} _houdini_105: bool;

const {:existential true} _houdini_106: bool;

const {:existential true} _houdini_107: bool;

const {:existential true} _houdini_108: bool;

const {:existential true} _houdini_109: bool;

const {:existential true} _houdini_110: bool;

const {:existential true} _houdini_111: bool;

const {:existential true} _houdini_112: bool;

const {:existential true} _houdini_113: bool;

const {:existential true} _houdini_114: bool;

procedure MS_Check__v1.encode_ie___v2.encode_ie(_v1.buf_.1: int, 
    _v1.bufsize_.1: int, 
    _v1.ie_.1: int, 
    _v1.ielen_.1: int, 
    _v1.leader_.1: int, 
    _v1.leader_len_.1: int, 
    _v2.buf_.1: int, 
    _v2.bufsize_.1: int, 
    _v2.ie_.1: int, 
    _v2.ielen_.1: int, 
    _v2.leader_.1: int, 
    _v2.leader_len_.1: int)
   returns (_v1.result.encode_ie$1: int, _v2.result.encode_ie$1: int);
  requires _houdini_81 ==> _v1.buf_.1 <= _v2.buf_.1;
  requires _houdini_82 ==> _v2.buf_.1 <= _v1.buf_.1;
  requires _houdini_83 ==> _v1.bufsize_.1 <= _v2.bufsize_.1;
  requires _houdini_84 ==> _v2.bufsize_.1 <= _v1.bufsize_.1;
  requires _houdini_85 ==> _v1.ie_.1 <= _v2.ie_.1;
  requires _houdini_86 ==> _v2.ie_.1 <= _v1.ie_.1;
  requires _houdini_87 ==> _v1.ielen_.1 <= _v2.ielen_.1;
  requires _houdini_88 ==> _v2.ielen_.1 <= _v1.ielen_.1;
  requires _houdini_89 ==> _v1.leader_.1 <= _v2.leader_.1;
  requires _houdini_90 ==> _v2.leader_.1 <= _v1.leader_.1;
  requires _houdini_91 ==> _v1.leader_len_.1 <= _v2.leader_len_.1;
  requires _houdini_92 ==> _v2.leader_len_.1 <= _v1.leader_len_.1;
  requires _houdini_93 ==> _v1.OK ==> _v2.OK;
  requires _houdini_94 ==> _v2.OK ==> _v1.OK;
  requires _houdini_95 ==> _v1.Mem == _v2.Mem;
  requires _houdini_96 ==> _v1.alloc <= _v2.alloc;
  requires _houdini_97 ==> _v2.alloc <= _v1.alloc;
  requires _houdini_98 ==> _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR;
  requires _houdini_99 ==> _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR;
  requires _houdini_100 ==> _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR;
  requires _houdini_101 ==> _v1.Mem_T.CHAR == _v2.Mem_T.CHAR;
  requires _houdini_102 ==> _v1.Mem_T.INT4 == _v2.Mem_T.INT4;
  requires _houdini_103 ==> _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR;
  requires _houdini_104 ==> _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR;
  requires _houdini_105 ==> _v1.Mem_T.PVOID == _v2.Mem_T.PVOID;
  requires _houdini_106
   ==> _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry;
  requires _houdini_107 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  requires _houdini_108 ==> _v1.Mem_T.VOID == _v2.Mem_T.VOID;
  requires _houdini_109
   ==> _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry;
  requires _houdini_110
   ==> _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
  requires _houdini_111 ==> _v1.detChoiceCnt <= _v2.detChoiceCnt;
  requires _houdini_112 ==> _v2.detChoiceCnt <= _v1.detChoiceCnt;
  requires _houdini_113 ==> _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE;
  requires _houdini_114 ==> _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.OK, _v1.Mem_T.UCHAR, _v2.OK, _v2.Mem_T.UCHAR;
  ensures MS$_v1.encode_ie$_v2.encode_ie(_v1.buf_.1, 
  _v1.bufsize_.1, 
  _v1.ie_.1, 
  _v1.ielen_.1, 
  _v1.leader_.1, 
  _v1.leader_len_.1, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.OK, 
  _v1.Mem_T.UCHAR, 
  _v1.result.encode_ie$1, 
  _v2.buf_.1, 
  _v2.bufsize_.1, 
  _v2.ie_.1, 
  _v2.ielen_.1, 
  _v2.leader_.1, 
  _v2.leader_len_.1, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.OK, 
  _v2.Mem_T.UCHAR, 
  _v2.result.encode_ie$1);
  ensures _houdini_76 ==> _v1.result.encode_ie$1 <= _v2.result.encode_ie$1;
  ensures _houdini_77 ==> _v2.result.encode_ie$1 <= _v1.result.encode_ie$1;
  ensures _houdini_78 ==> _v1.OK ==> _v2.OK;
  ensures _houdini_79 ==> _v2.OK ==> _v1.OK;
  ensures _houdini_80 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;



implementation MS_Check__v1.encode_ie___v2.encode_ie(_v1.buf_.1: int, 
    _v1.bufsize_.1: int, 
    _v1.ie_.1: int, 
    _v1.ielen_.1: int, 
    _v1.leader_.1: int, 
    _v1.leader_len_.1: int, 
    _v2.buf_.1: int, 
    _v2.bufsize_.1: int, 
    _v2.ie_.1: int, 
    _v2.ielen_.1: int, 
    _v2.leader_.1: int, 
    _v2.leader_len_.1: int)
   returns (_v1.result.encode_ie$1: int, _v2.result.encode_ie$1: int)
{
  var inline$_v1.encode_ie$0$havoc_stringTemp: int;
  var inline$_v1.encode_ie$0$condVal: int;
  var inline$_v1.encode_ie$0$buf: int;
  var inline$_v1.encode_ie$0$bufsize: int;
  var inline$_v1.encode_ie$0$i: int;
  var inline$_v1.encode_ie$0$ie: int;
  var inline$_v1.encode_ie$0$ielen: int;
  var inline$_v1.encode_ie$0$leader: int;
  var inline$_v1.encode_ie$0$leader_len: int;
  var inline$_v1.encode_ie$0$p: int;
  var inline$_v1.encode_ie$0$result.memcpy$2: int;
  var inline$_v1.encode_ie$0$$result.question.3.$$static$: int;
  var inline$_v1.encode_ie$0$tempBoogie0: int;
  var inline$_v1.encode_ie$0$tempBoogie1: int;
  var inline$_v1.encode_ie$0$tempBoogie2: int;
  var inline$_v1.encode_ie$0$tempBoogie3: int;
  var inline$_v1.encode_ie$0$tempBoogie4: int;
  var inline$_v1.encode_ie$0$tempBoogie5: int;
  var inline$_v1.encode_ie$0$tempBoogie6: int;
  var inline$_v1.encode_ie$0$tempBoogie7: int;
  var inline$_v1.encode_ie$0$tempBoogie8: int;
  var inline$_v1.encode_ie$0$tempBoogie9: int;
  var inline$_v1.encode_ie$0$tempBoogie10: int;
  var inline$_v1.encode_ie$0$tempBoogie11: int;
  var inline$_v1.encode_ie$0$tempBoogie12: int;
  var inline$_v1.encode_ie$0$tempBoogie13: int;
  var inline$_v1.encode_ie$0$tempBoogie14: int;
  var inline$_v1.encode_ie$0$tempBoogie15: int;
  var inline$_v1.encode_ie$0$tempBoogie16: int;
  var inline$_v1.encode_ie$0$tempBoogie17: int;
  var inline$_v1.encode_ie$0$tempBoogie18: int;
  var inline$_v1.encode_ie$0$tempBoogie19: int;
  var inline$_v1.encode_ie$0$__havoc_dummy_return: int;
  var inline$_v1.encode_ie$0$buf_.1: int;
  var inline$_v1.encode_ie$0$bufsize_.1: int;
  var inline$_v1.encode_ie$0$ie_.1: int;
  var inline$_v1.encode_ie$0$ielen_.1: int;
  var inline$_v1.encode_ie$0$leader_.1: int;
  var inline$_v1.encode_ie$0$leader_len_.1: int;
  var inline$_v1.encode_ie$0$result.encode_ie$1: int;
  var inline$_v1.encode_ie$0$_v1.OK: bool;
  var inline$_v1.encode_ie$0$_v1.Mem_T.UCHAR: [int]int;
  var inline$_v2.encode_ie$0$havoc_stringTemp: int;
  var inline$_v2.encode_ie$0$condVal: int;
  var inline$_v2.encode_ie$0$buf: int;
  var inline$_v2.encode_ie$0$bufsize: int;
  var inline$_v2.encode_ie$0$i: int;
  var inline$_v2.encode_ie$0$ie: int;
  var inline$_v2.encode_ie$0$ielen: int;
  var inline$_v2.encode_ie$0$leader: int;
  var inline$_v2.encode_ie$0$leader_len: int;
  var inline$_v2.encode_ie$0$p: int;
  var inline$_v2.encode_ie$0$result.memcpy$2: int;
  var inline$_v2.encode_ie$0$$result.question.3.$$static$: int;
  var inline$_v2.encode_ie$0$tempBoogie0: int;
  var inline$_v2.encode_ie$0$tempBoogie1: int;
  var inline$_v2.encode_ie$0$tempBoogie2: int;
  var inline$_v2.encode_ie$0$tempBoogie3: int;
  var inline$_v2.encode_ie$0$tempBoogie4: int;
  var inline$_v2.encode_ie$0$tempBoogie5: int;
  var inline$_v2.encode_ie$0$tempBoogie6: int;
  var inline$_v2.encode_ie$0$tempBoogie7: int;
  var inline$_v2.encode_ie$0$tempBoogie8: int;
  var inline$_v2.encode_ie$0$tempBoogie9: int;
  var inline$_v2.encode_ie$0$tempBoogie10: int;
  var inline$_v2.encode_ie$0$tempBoogie11: int;
  var inline$_v2.encode_ie$0$tempBoogie12: int;
  var inline$_v2.encode_ie$0$tempBoogie13: int;
  var inline$_v2.encode_ie$0$tempBoogie14: int;
  var inline$_v2.encode_ie$0$tempBoogie15: int;
  var inline$_v2.encode_ie$0$tempBoogie16: int;
  var inline$_v2.encode_ie$0$tempBoogie17: int;
  var inline$_v2.encode_ie$0$tempBoogie18: int;
  var inline$_v2.encode_ie$0$tempBoogie19: int;
  var inline$_v2.encode_ie$0$__havoc_dummy_return: int;
  var inline$_v2.encode_ie$0$buf_.1: int;
  var inline$_v2.encode_ie$0$bufsize_.1: int;
  var inline$_v2.encode_ie$0$ie_.1: int;
  var inline$_v2.encode_ie$0$ielen_.1: int;
  var inline$_v2.encode_ie$0$leader_.1: int;
  var inline$_v2.encode_ie$0$leader_len_.1: int;
  var inline$_v2.encode_ie$0$result.encode_ie$1: int;
  var inline$_v2.encode_ie$0$_v2.OK: bool;
  var inline$_v2.encode_ie$0$_v2.Mem_T.UCHAR: [int]int;
  var _v1.memcpy_1_done: bool;
  var _v1.memcpy_in_1_0: int;
  var _v1.memcpy_in_1_1: int;
  var _v1.memcpy_in_1_2: int;
  var _v1.memcpy_in_1_3: bool;
  var _v1.memcpy_in_1_4: [int]int;
  var _v1.memcpy_out_1_0: int;
  var _v1.encode_ie_loop_label_14_head_2_done: bool;
  var _v1.encode_ie_loop_label_14_head_in_2_0: int;
  var _v1.encode_ie_loop_label_14_head_in_2_1: int;
  var _v1.encode_ie_loop_label_14_head_in_2_2: int;
  var _v1.encode_ie_loop_label_14_head_in_2_3: int;
  var _v1.encode_ie_loop_label_14_head_in_2_4: int;
  var _v1.encode_ie_loop_label_14_head_in_2_5: bool;
  var _v1.encode_ie_loop_label_14_head_in_2_6: [int]int;
  var _v1.encode_ie_loop_label_14_head_out_2_0: int;
  var _v1.encode_ie_loop_label_14_head_out_2_1: int;
  var _v1.encode_ie_loop_label_14_head_out_2_2: int;
  var _v1.encode_ie_loop_label_14_head_out_2_3: [int]int;
  var _v1.encode_ie_loop_label_14_head_out_2_4: bool;
  var _v2.memcpy_3_done: bool;
  var _v2.memcpy_in_3_0: int;
  var _v2.memcpy_in_3_1: int;
  var _v2.memcpy_in_3_2: int;
  var _v2.memcpy_in_3_3: bool;
  var _v2.memcpy_in_3_4: [int]int;
  var _v2.memcpy_out_3_0: int;
  var _v2.encode_ie_loop_label_14_head_4_done: bool;
  var _v2.encode_ie_loop_label_14_head_in_4_0: int;
  var _v2.encode_ie_loop_label_14_head_in_4_1: int;
  var _v2.encode_ie_loop_label_14_head_in_4_2: int;
  var _v2.encode_ie_loop_label_14_head_in_4_3: int;
  var _v2.encode_ie_loop_label_14_head_in_4_4: int;
  var _v2.encode_ie_loop_label_14_head_in_4_5: bool;
  var _v2.encode_ie_loop_label_14_head_in_4_6: [int]int;
  var _v2.encode_ie_loop_label_14_head_out_4_0: int;
  var _v2.encode_ie_loop_label_14_head_out_4_1: int;
  var _v2.encode_ie_loop_label_14_head_out_4_2: int;
  var _v2.encode_ie_loop_label_14_head_out_4_3: int;
  var _v2.encode_ie_loop_label_14_head_out_4_4: [int]int;
  var _v2.encode_ie_loop_label_14_head_out_4_5: bool;
  var store__0__v1.OK: bool;
  var store__0__v1.Mem_T.UCHAR: [int]int;
  var store__0__v2.OK: bool;
  var store__0__v2.Mem_T.UCHAR: [int]int;
  var out__v1.memcpy_out_1_0_0: int;
  var out__v2.memcpy_out_3_0_0: int;
  var store__1__v1.OK: bool;
  var store__1__v1.Mem_T.UCHAR: [int]int;
  var store__1__v2.OK: bool;
  var store__1__v2.Mem_T.UCHAR: [int]int;
  var out__v1.encode_ie_loop_label_14_head_out_2_0_1: int;
  var out__v1.encode_ie_loop_label_14_head_out_2_1_1: int;
  var out__v1.encode_ie_loop_label_14_head_out_2_2_1: int;
  var out__v2.encode_ie_loop_label_14_head_out_4_0_1: int;
  var out__v2.encode_ie_loop_label_14_head_out_4_1_1: int;
  var out__v2.encode_ie_loop_label_14_head_out_4_2_1: int;
  var out__v2.encode_ie_loop_label_14_head_out_4_3_1: int;

  START:
    _v1.memcpy_1_done, _v1.encode_ie_loop_label_14_head_2_done, _v2.memcpy_3_done, _v2.encode_ie_loop_label_14_head_4_done := false, false, false, false;
    goto inline$_v1.encode_ie$0$Entry;

  inline$_v1.encode_ie$0$Entry:
    inline$_v1.encode_ie$0$buf_.1 := _v1.buf_.1;
    inline$_v1.encode_ie$0$bufsize_.1 := _v1.bufsize_.1;
    inline$_v1.encode_ie$0$ie_.1 := _v1.ie_.1;
    inline$_v1.encode_ie$0$ielen_.1 := _v1.ielen_.1;
    inline$_v1.encode_ie$0$leader_.1 := _v1.leader_.1;
    inline$_v1.encode_ie$0$leader_len_.1 := _v1.leader_len_.1;
    havoc inline$_v1.encode_ie$0$havoc_stringTemp, inline$_v1.encode_ie$0$condVal, inline$_v1.encode_ie$0$buf, inline$_v1.encode_ie$0$bufsize, inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ie, inline$_v1.encode_ie$0$ielen, inline$_v1.encode_ie$0$leader, inline$_v1.encode_ie$0$leader_len, inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$result.memcpy$2, inline$_v1.encode_ie$0$$result.question.3.$$static$, inline$_v1.encode_ie$0$tempBoogie0, inline$_v1.encode_ie$0$tempBoogie1, inline$_v1.encode_ie$0$tempBoogie2, inline$_v1.encode_ie$0$tempBoogie3, inline$_v1.encode_ie$0$tempBoogie4, inline$_v1.encode_ie$0$tempBoogie5, inline$_v1.encode_ie$0$tempBoogie6, inline$_v1.encode_ie$0$tempBoogie7, inline$_v1.encode_ie$0$tempBoogie8, inline$_v1.encode_ie$0$tempBoogie9, inline$_v1.encode_ie$0$tempBoogie10, inline$_v1.encode_ie$0$tempBoogie11, inline$_v1.encode_ie$0$tempBoogie12, inline$_v1.encode_ie$0$tempBoogie13, inline$_v1.encode_ie$0$tempBoogie14, inline$_v1.encode_ie$0$tempBoogie15, inline$_v1.encode_ie$0$tempBoogie16, inline$_v1.encode_ie$0$tempBoogie17, inline$_v1.encode_ie$0$tempBoogie18, inline$_v1.encode_ie$0$tempBoogie19, inline$_v1.encode_ie$0$__havoc_dummy_return, inline$_v1.encode_ie$0$result.encode_ie$1;
    inline$_v1.encode_ie$0$_v1.OK := _v1.OK;
    inline$_v1.encode_ie$0$_v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR;
    goto inline$_v1.encode_ie$0$anon0#2;

  inline$_v1.encode_ie$0$anon0#2:
    inline$_v1.encode_ie$0$havoc_stringTemp := 0;
    goto inline$_v1.encode_ie$0$start#2;

  inline$_v1.encode_ie$0$start#2:
    assume _v2.INT_LT(inline$_v1.encode_ie$0$buf_.1, _v1.alloc);
    assume _v2.INT_LT(inline$_v1.encode_ie$0$ie_.1, _v1.alloc);
    assume _v2.INT_LT(inline$_v1.encode_ie$0$leader_.1, _v1.alloc);
    inline$_v1.encode_ie$0$buf := 0;
    assume _v2.INT_GEQ(inline$_v1.encode_ie$0$buf_.1, 0);
    inline$_v1.encode_ie$0$bufsize := 0;
    inline$_v1.encode_ie$0$i := 0;
    inline$_v1.encode_ie$0$ie := 0;
    assume _v2.INT_GEQ(inline$_v1.encode_ie$0$ie_.1, 0);
    inline$_v1.encode_ie$0$ielen := 0;
    inline$_v1.encode_ie$0$leader := 0;
    assume _v2.INT_GEQ(inline$_v1.encode_ie$0$leader_.1, 0);
    inline$_v1.encode_ie$0$leader_len := 0;
    inline$_v1.encode_ie$0$p := 0;
    inline$_v1.encode_ie$0$result.encode_ie$1 := 0;
    inline$_v1.encode_ie$0$result.memcpy$2 := 0;
    inline$_v1.encode_ie$0$$result.question.3.$$static$ := 0;
    inline$_v1.encode_ie$0$buf := inline$_v1.encode_ie$0$buf_.1;
    inline$_v1.encode_ie$0$bufsize := inline$_v1.encode_ie$0$bufsize_.1;
    inline$_v1.encode_ie$0$ie := inline$_v1.encode_ie$0$ie_.1;
    inline$_v1.encode_ie$0$ielen := inline$_v1.encode_ie$0$ielen_.1;
    inline$_v1.encode_ie$0$leader := inline$_v1.encode_ie$0$leader_.1;
    inline$_v1.encode_ie$0$leader_len := inline$_v1.encode_ie$0$leader_len_.1;
    goto inline$_v1.encode_ie$0$label_3#2;

  inline$_v1.encode_ie$0$label_3#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 9} true;
    goto inline$_v1.encode_ie$0$label_4#2;

  inline$_v1.encode_ie$0$label_4#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 10} true;
    goto inline$_v1.encode_ie$0$label_5#2;

  inline$_v1.encode_ie$0$label_5#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 13} true;
    goto inline$_v1.encode_ie$0$label_5_true#2, inline$_v1.encode_ie$0$label_5_false#2;

  inline$_v1.encode_ie$0$label_5_false#2:
    assume !_v2.INT_LT(inline$_v1.encode_ie$0$bufsize, inline$_v1.encode_ie$0$leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_1, inline$_v1.encode_ie$0$bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_2, inline$_v1.encode_ie$0$leader_len);
    goto inline$_v1.encode_ie$0$label_6#2;

  inline$_v1.encode_ie$0$label_6#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 15} true;
    inline$_v1.encode_ie$0$p := inline$_v1.encode_ie$0$buf;
    assume _v2.value_is(_v1.__ctobpl_const_3, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_4, inline$_v1.encode_ie$0$buf);
    goto inline$_v1.encode_ie$0$label_8#2;

  inline$_v1.encode_ie$0$label_8#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 16} true;
    _v1.memcpy_in_1_0, _v1.memcpy_in_1_1, _v1.memcpy_in_1_2, _v1.memcpy_in_1_3, _v1.memcpy_in_1_4 := inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$leader, inline$_v1.encode_ie$0$leader_len, _v1.OK, _v1.Mem_T.UCHAR;
    call inline$_v1.encode_ie$0$result.memcpy$2 := _v1.memcpy(inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$leader, inline$_v1.encode_ie$0$leader_len);
    _v1.memcpy_1_done := true;
    _v1.memcpy_out_1_0 := inline$_v1.encode_ie$0$result.memcpy$2;
    assume _v2.value_is(_v1.__ctobpl_const_5, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_6, inline$_v1.encode_ie$0$leader);
    assume _v2.value_is(_v1.__ctobpl_const_7, inline$_v1.encode_ie$0$leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_8, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_9, inline$_v1.encode_ie$0$leader);
    assume _v2.value_is(_v1.__ctobpl_const_10, inline$_v1.encode_ie$0$leader_len);
    goto inline$_v1.encode_ie$0$label_11#2;

  inline$_v1.encode_ie$0$label_11#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 17} true;
    havoc inline$_v1.encode_ie$0$tempBoogie0;    
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(inline$_v1.encode_ie$0$bufsize, inline$_v1.encode_ie$0$leader_len, 1, inline$_v1.encode_ie$0$tempBoogie0);
    inline$_v1.encode_ie$0$bufsize := inline$_v1.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_11, inline$_v1.encode_ie$0$bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_12, inline$_v1.encode_ie$0$leader_len);
    goto inline$_v1.encode_ie$0$label_12#2;

  inline$_v1.encode_ie$0$label_12#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 18} true;
    inline$_v1.encode_ie$0$tempBoogie0 := _v2.INT_PLUS(inline$_v1.encode_ie$0$p, 1, inline$_v1.encode_ie$0$leader_len);
    inline$_v1.encode_ie$0$p := inline$_v1.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_13, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_14, inline$_v1.encode_ie$0$leader_len);
    goto inline$_v1.encode_ie$0$label_13#2;

  inline$_v1.encode_ie$0$label_13#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    inline$_v1.encode_ie$0$i := 0;
    assume _v2.value_is(_v1.__ctobpl_const_15, inline$_v1.encode_ie$0$i);
    goto inline$_v1.encode_ie$0$label_14#2;

  inline$_v1.encode_ie$0$label_14#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    goto inline$_v1.encode_ie$0$label_14_head#2;

  inline$_v1.encode_ie$0$label_14_head#2:
    _v1.encode_ie_loop_label_14_head_in_2_0, _v1.encode_ie_loop_label_14_head_in_2_1, _v1.encode_ie_loop_label_14_head_in_2_2, _v1.encode_ie_loop_label_14_head_in_2_3, _v1.encode_ie_loop_label_14_head_in_2_4, _v1.encode_ie_loop_label_14_head_in_2_5, _v1.encode_ie_loop_label_14_head_in_2_6 := inline$_v1.encode_ie$0$bufsize, inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ielen, inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$tempBoogie0, _v1.OK, _v1.Mem_T.UCHAR;
    call inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$tempBoogie0 := _v1.encode_ie_loop_label_14_head(inline$_v1.encode_ie$0$bufsize, inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ielen, inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$tempBoogie0);
    _v1.encode_ie_loop_label_14_head_2_done := true;
    _v1.encode_ie_loop_label_14_head_out_2_0, _v1.encode_ie_loop_label_14_head_out_2_1, _v1.encode_ie_loop_label_14_head_out_2_2, _v1.encode_ie_loop_label_14_head_out_2_3, _v1.encode_ie_loop_label_14_head_out_2_4 := inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$tempBoogie0, _v1.Mem_T.UCHAR, _v1.OK;
    goto inline$_v1.encode_ie$0$label_14_head_last#2;

  inline$_v1.encode_ie$0$label_14_head_last#2:
    goto inline$_v1.encode_ie$0$label_14_true#2, inline$_v1.encode_ie$0$label_14_false#2;

  inline$_v1.encode_ie$0$label_14_false#2:
    assume !_v2.INT_LT(inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, inline$_v1.encode_ie$0$i);
    assume _v2.value_is(_v1.__ctobpl_const_17, inline$_v1.encode_ie$0$ielen);
    goto inline$_v1.encode_ie$0$label_15#2;

  inline$_v1.encode_ie$0$label_14_true#2:
    assume _v2.INT_LT(inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, inline$_v1.encode_ie$0$i);
    assume _v2.value_is(_v1.__ctobpl_const_17, inline$_v1.encode_ie$0$ielen);
    goto inline$_v1.encode_ie$0$label_16#2;

  inline$_v1.encode_ie$0$label_16#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    goto inline$_v1.encode_ie$0$label_16_true#2, inline$_v1.encode_ie$0$label_16_false#2;

  inline$_v1.encode_ie$0$label_16_false#2:
    assume !_v2.INT_LT(2, inline$_v1.encode_ie$0$bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, inline$_v1.encode_ie$0$bufsize);
    goto inline$_v1.encode_ie$0$label_15#2;

  inline$_v1.encode_ie$0$label_15#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    goto inline$_v1.encode_ie$0$label_15_true#2, inline$_v1.encode_ie$0$label_15_false#2;

  inline$_v1.encode_ie$0$label_15_false#2:
    assume !_v2.INT_EQ(inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ielen);
    assume _v2.value_is(_v1.__ctobpl_const_18, inline$_v1.encode_ie$0$i);
    assume _v2.value_is(_v1.__ctobpl_const_19, inline$_v1.encode_ie$0$ielen);
    goto inline$_v1.encode_ie$0$label_21#2;

  inline$_v1.encode_ie$0$label_21#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    inline$_v1.encode_ie$0$$result.question.3.$$static$ := 0;
    assume _v2.value_is(_v1.__ctobpl_const_27, inline$_v1.encode_ie$0$$result.question.3.$$static$);
    goto inline$_v1.encode_ie$0$label_23#2;

  inline$_v1.encode_ie$0$label_15_true#2:
    assume _v2.INT_EQ(inline$_v1.encode_ie$0$i, inline$_v1.encode_ie$0$ielen);
    assume _v2.value_is(_v1.__ctobpl_const_18, inline$_v1.encode_ie$0$i);
    assume _v2.value_is(_v1.__ctobpl_const_19, inline$_v1.encode_ie$0$ielen);
    goto inline$_v1.encode_ie$0$label_22#2;

  inline$_v1.encode_ie$0$label_22#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    havoc inline$_v1.encode_ie$0$$result.question.3.$$static$;    
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(inline$_v1.encode_ie$0$p, inline$_v1.encode_ie$0$buf, 1, inline$_v1.encode_ie$0$$result.question.3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_28, inline$_v1.encode_ie$0$$result.question.3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_29, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_30, inline$_v1.encode_ie$0$buf);
    goto inline$_v1.encode_ie$0$label_23#2;

  inline$_v1.encode_ie$0$label_23#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 38} true;
    inline$_v1.encode_ie$0$result.encode_ie$1 := inline$_v1.encode_ie$0$$result.question.3.$$static$;
    assume _v2.value_is(_v1.__ctobpl_const_31, inline$_v1.encode_ie$0$$result.question.3.$$static$);
    goto inline$_v1.encode_ie$0$label_1#2;

  inline$_v1.encode_ie$0$label_16_true#2:
    assume _v2.INT_LT(2, inline$_v1.encode_ie$0$bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, inline$_v1.encode_ie$0$bufsize);
    goto inline$_v1.encode_ie$0$label_17#2;

  inline$_v1.encode_ie$0$label_17#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(inline$_v1.encode_ie$0$p, 0);
    _v1.OK := _v1.OK && _v2.Res_VALID_REGION(inline$_v1.encode_ie$0$p) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[inline$_v1.encode_ie$0$p := 120];
    assume _v2.value_is(_v1.__ctobpl_const_21, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_22, _v1.Mem_T.UCHAR[inline$_v1.encode_ie$0$p]);
    goto inline$_v1.encode_ie$0$label_18#2;

  inline$_v1.encode_ie$0$label_18#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(inline$_v1.encode_ie$0$p, 1, 1), 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(inline$_v1.encode_ie$0$p, 1, 1)) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v1.encode_ie$0$p, 1, 1) := 120];
    assume _v2.value_is(_v1.__ctobpl_const_23, inline$_v1.encode_ie$0$p);
    assume _v2.value_is(_v1.__ctobpl_const_24, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v1.encode_ie$0$p, 1, 1)]);
    goto inline$_v1.encode_ie$0$label_19#2;

  inline$_v1.encode_ie$0$label_19#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 33} true;
    inline$_v1.encode_ie$0$tempBoogie0 := _v2.INT_PLUS(inline$_v1.encode_ie$0$p, 1, 2);
    inline$_v1.encode_ie$0$p := inline$_v1.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_25, inline$_v1.encode_ie$0$p);
    goto inline$_v1.encode_ie$0$label_20#2;

  inline$_v1.encode_ie$0$label_20#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    assume _v2.value_is(_v1.__ctobpl_const_26, inline$_v1.encode_ie$0$i);
    inline$_v1.encode_ie$0$i := _v2.INT_PLUS(inline$_v1.encode_ie$0$i, 1, 1);
    goto inline$_v1.encode_ie$0$label_20_dummy#2;

  inline$_v1.encode_ie$0$label_20_dummy#2:
    assume false;
    goto inline$_v1.encode_ie$0$Return;

  inline$_v1.encode_ie$0$label_5_true#2:
    assume _v2.INT_LT(inline$_v1.encode_ie$0$bufsize, inline$_v1.encode_ie$0$leader_len);
    assume _v2.value_is(_v1.__ctobpl_const_1, inline$_v1.encode_ie$0$bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_2, inline$_v1.encode_ie$0$leader_len);
    goto inline$_v1.encode_ie$0$label_7#2;

  inline$_v1.encode_ie$0$label_7#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 14} true;
    inline$_v1.encode_ie$0$result.encode_ie$1 := 0;
    goto inline$_v1.encode_ie$0$label_1#2;

  inline$_v1.encode_ie$0$label_1#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 39} true;
    goto inline$_v1.encode_ie$0$Return;

  inline$_v1.encode_ie$0$Return:
    assume true;
    _v1.result.encode_ie$1 := inline$_v1.encode_ie$0$result.encode_ie$1;
    goto START$1;

  START$1:
    goto inline$_v2.encode_ie$0$Entry;

  inline$_v2.encode_ie$0$Entry:
    inline$_v2.encode_ie$0$buf_.1 := _v2.buf_.1;
    inline$_v2.encode_ie$0$bufsize_.1 := _v2.bufsize_.1;
    inline$_v2.encode_ie$0$ie_.1 := _v2.ie_.1;
    inline$_v2.encode_ie$0$ielen_.1 := _v2.ielen_.1;
    inline$_v2.encode_ie$0$leader_.1 := _v2.leader_.1;
    inline$_v2.encode_ie$0$leader_len_.1 := _v2.leader_len_.1;
    havoc inline$_v2.encode_ie$0$havoc_stringTemp, inline$_v2.encode_ie$0$condVal, inline$_v2.encode_ie$0$buf, inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ie, inline$_v2.encode_ie$0$ielen, inline$_v2.encode_ie$0$leader, inline$_v2.encode_ie$0$leader_len, inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$result.memcpy$2, inline$_v2.encode_ie$0$$result.question.3.$$static$, inline$_v2.encode_ie$0$tempBoogie0, inline$_v2.encode_ie$0$tempBoogie1, inline$_v2.encode_ie$0$tempBoogie2, inline$_v2.encode_ie$0$tempBoogie3, inline$_v2.encode_ie$0$tempBoogie4, inline$_v2.encode_ie$0$tempBoogie5, inline$_v2.encode_ie$0$tempBoogie6, inline$_v2.encode_ie$0$tempBoogie7, inline$_v2.encode_ie$0$tempBoogie8, inline$_v2.encode_ie$0$tempBoogie9, inline$_v2.encode_ie$0$tempBoogie10, inline$_v2.encode_ie$0$tempBoogie11, inline$_v2.encode_ie$0$tempBoogie12, inline$_v2.encode_ie$0$tempBoogie13, inline$_v2.encode_ie$0$tempBoogie14, inline$_v2.encode_ie$0$tempBoogie15, inline$_v2.encode_ie$0$tempBoogie16, inline$_v2.encode_ie$0$tempBoogie17, inline$_v2.encode_ie$0$tempBoogie18, inline$_v2.encode_ie$0$tempBoogie19, inline$_v2.encode_ie$0$__havoc_dummy_return, inline$_v2.encode_ie$0$result.encode_ie$1;
    inline$_v2.encode_ie$0$_v2.OK := _v2.OK;
    inline$_v2.encode_ie$0$_v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR;
    goto inline$_v2.encode_ie$0$anon0#2;

  inline$_v2.encode_ie$0$anon0#2:
    inline$_v2.encode_ie$0$havoc_stringTemp := 0;
    goto inline$_v2.encode_ie$0$start#2;

  inline$_v2.encode_ie$0$start#2:
    assume _v2.INT_LT(inline$_v2.encode_ie$0$buf_.1, _v2.alloc);
    assume _v2.INT_LT(inline$_v2.encode_ie$0$ie_.1, _v2.alloc);
    assume _v2.INT_LT(inline$_v2.encode_ie$0$leader_.1, _v2.alloc);
    inline$_v2.encode_ie$0$buf := 0;
    assume _v2.INT_GEQ(inline$_v2.encode_ie$0$buf_.1, 0);
    inline$_v2.encode_ie$0$bufsize := 0;
    inline$_v2.encode_ie$0$i := 0;
    inline$_v2.encode_ie$0$ie := 0;
    assume _v2.INT_GEQ(inline$_v2.encode_ie$0$ie_.1, 0);
    inline$_v2.encode_ie$0$ielen := 0;
    inline$_v2.encode_ie$0$leader := 0;
    assume _v2.INT_GEQ(inline$_v2.encode_ie$0$leader_.1, 0);
    inline$_v2.encode_ie$0$leader_len := 0;
    inline$_v2.encode_ie$0$p := 0;
    inline$_v2.encode_ie$0$result.encode_ie$1 := 0;
    inline$_v2.encode_ie$0$result.memcpy$2 := 0;
    inline$_v2.encode_ie$0$$result.question.3.$$static$ := 0;
    inline$_v2.encode_ie$0$buf := inline$_v2.encode_ie$0$buf_.1;
    inline$_v2.encode_ie$0$bufsize := inline$_v2.encode_ie$0$bufsize_.1;
    inline$_v2.encode_ie$0$ie := inline$_v2.encode_ie$0$ie_.1;
    inline$_v2.encode_ie$0$ielen := inline$_v2.encode_ie$0$ielen_.1;
    inline$_v2.encode_ie$0$leader := inline$_v2.encode_ie$0$leader_.1;
    inline$_v2.encode_ie$0$leader_len := inline$_v2.encode_ie$0$leader_len_.1;
    goto inline$_v2.encode_ie$0$label_3#2;

  inline$_v2.encode_ie$0$label_3#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 9} true;
    goto inline$_v2.encode_ie$0$label_4#2;

  inline$_v2.encode_ie$0$label_4#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 10} true;
    goto inline$_v2.encode_ie$0$label_5#2;

  inline$_v2.encode_ie$0$label_5#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 13} true;
    goto inline$_v2.encode_ie$0$label_5_true#2, inline$_v2.encode_ie$0$label_5_false#2;

  inline$_v2.encode_ie$0$label_5_false#2:
    assume !_v2.INT_LT(inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_1, inline$_v2.encode_ie$0$bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_2, inline$_v2.encode_ie$0$leader_len);
    goto inline$_v2.encode_ie$0$label_6#2;

  inline$_v2.encode_ie$0$label_6#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 15} true;
    inline$_v2.encode_ie$0$p := inline$_v2.encode_ie$0$buf;
    assume _v2.value_is(_v2.__ctobpl_const_3, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_4, inline$_v2.encode_ie$0$buf);
    goto inline$_v2.encode_ie$0$label_8#2;

  inline$_v2.encode_ie$0$label_8#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 16} true;
    _v2.memcpy_in_3_0, _v2.memcpy_in_3_1, _v2.memcpy_in_3_2, _v2.memcpy_in_3_3, _v2.memcpy_in_3_4 := inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$leader, inline$_v2.encode_ie$0$leader_len, _v2.OK, _v2.Mem_T.UCHAR;
    call inline$_v2.encode_ie$0$result.memcpy$2 := _v2.memcpy(inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$leader, inline$_v2.encode_ie$0$leader_len);
    _v2.memcpy_3_done := true;
    _v2.memcpy_out_3_0 := inline$_v2.encode_ie$0$result.memcpy$2;
    assume _v2.value_is(_v2.__ctobpl_const_5, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_6, inline$_v2.encode_ie$0$leader);
    assume _v2.value_is(_v2.__ctobpl_const_7, inline$_v2.encode_ie$0$leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_8, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_9, inline$_v2.encode_ie$0$leader);
    assume _v2.value_is(_v2.__ctobpl_const_10, inline$_v2.encode_ie$0$leader_len);
    goto inline$_v2.encode_ie$0$label_11#2;

  inline$_v2.encode_ie$0$label_11#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 17} true;
    havoc inline$_v2.encode_ie$0$tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$leader_len, 1, inline$_v2.encode_ie$0$tempBoogie0);
    inline$_v2.encode_ie$0$bufsize := inline$_v2.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_11, inline$_v2.encode_ie$0$bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_12, inline$_v2.encode_ie$0$leader_len);
    goto inline$_v2.encode_ie$0$label_12#2;

  inline$_v2.encode_ie$0$label_12#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 18} true;
    inline$_v2.encode_ie$0$tempBoogie0 := _v2.INT_PLUS(inline$_v2.encode_ie$0$p, 1, inline$_v2.encode_ie$0$leader_len);
    inline$_v2.encode_ie$0$p := inline$_v2.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_13, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_14, inline$_v2.encode_ie$0$leader_len);
    goto inline$_v2.encode_ie$0$label_13#2;

  inline$_v2.encode_ie$0$label_13#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    inline$_v2.encode_ie$0$i := 0;
    assume _v2.value_is(_v2.__ctobpl_const_15, inline$_v2.encode_ie$0$i);
    goto inline$_v2.encode_ie$0$label_14#2;

  inline$_v2.encode_ie$0$label_14#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    goto inline$_v2.encode_ie$0$label_14_head#2;

  inline$_v2.encode_ie$0$label_14_head#2:
    _v2.encode_ie_loop_label_14_head_in_4_0, _v2.encode_ie_loop_label_14_head_in_4_1, _v2.encode_ie_loop_label_14_head_in_4_2, _v2.encode_ie_loop_label_14_head_in_4_3, _v2.encode_ie_loop_label_14_head_in_4_4, _v2.encode_ie_loop_label_14_head_in_4_5, _v2.encode_ie_loop_label_14_head_in_4_6 := inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ielen, inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$tempBoogie0, _v2.OK, _v2.Mem_T.UCHAR;
    call inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$tempBoogie0 := _v2.encode_ie_loop_label_14_head(inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ielen, inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$tempBoogie0);
    _v2.encode_ie_loop_label_14_head_4_done := true;
    _v2.encode_ie_loop_label_14_head_out_4_0, _v2.encode_ie_loop_label_14_head_out_4_1, _v2.encode_ie_loop_label_14_head_out_4_2, _v2.encode_ie_loop_label_14_head_out_4_3, _v2.encode_ie_loop_label_14_head_out_4_4, _v2.encode_ie_loop_label_14_head_out_4_5 := inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$tempBoogie0, _v2.Mem_T.UCHAR, _v2.OK;
    goto inline$_v2.encode_ie$0$label_14_head_last#2;

  inline$_v2.encode_ie$0$label_14_head_last#2:
    goto inline$_v2.encode_ie$0$label_14_true#2, inline$_v2.encode_ie$0$label_14_false#2;

  inline$_v2.encode_ie$0$label_14_false#2:
    assume !_v2.INT_LT(inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, inline$_v2.encode_ie$0$i);
    assume _v2.value_is(_v2.__ctobpl_const_17, inline$_v2.encode_ie$0$ielen);
    goto inline$_v2.encode_ie$0$label_15#2;

  inline$_v2.encode_ie$0$label_14_true#2:
    assume _v2.INT_LT(inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, inline$_v2.encode_ie$0$i);
    assume _v2.value_is(_v2.__ctobpl_const_17, inline$_v2.encode_ie$0$ielen);
    goto inline$_v2.encode_ie$0$label_16#2;

  inline$_v2.encode_ie$0$label_16#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    goto inline$_v2.encode_ie$0$label_16_true#2, inline$_v2.encode_ie$0$label_16_false#2;

  inline$_v2.encode_ie$0$label_16_false#2:
    assume !_v2.INT_LT(2, inline$_v2.encode_ie$0$bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, inline$_v2.encode_ie$0$bufsize);
    goto inline$_v2.encode_ie$0$label_15#2;

  inline$_v2.encode_ie$0$label_15#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    goto inline$_v2.encode_ie$0$label_15_true#2, inline$_v2.encode_ie$0$label_15_false#2;

  inline$_v2.encode_ie$0$label_15_false#2:
    assume !_v2.INT_EQ(inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ielen);
    assume _v2.value_is(_v2.__ctobpl_const_18, inline$_v2.encode_ie$0$i);
    assume _v2.value_is(_v2.__ctobpl_const_19, inline$_v2.encode_ie$0$ielen);
    goto inline$_v2.encode_ie$0$label_22#2;

  inline$_v2.encode_ie$0$label_22#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    inline$_v2.encode_ie$0$$result.question.3.$$static$ := 0;
    assume _v2.value_is(_v2.__ctobpl_const_28, inline$_v2.encode_ie$0$$result.question.3.$$static$);
    goto inline$_v2.encode_ie$0$label_24#2;

  inline$_v2.encode_ie$0$label_15_true#2:
    assume _v2.INT_EQ(inline$_v2.encode_ie$0$i, inline$_v2.encode_ie$0$ielen);
    assume _v2.value_is(_v2.__ctobpl_const_18, inline$_v2.encode_ie$0$i);
    assume _v2.value_is(_v2.__ctobpl_const_19, inline$_v2.encode_ie$0$ielen);
    goto inline$_v2.encode_ie$0$label_23#2;

  inline$_v2.encode_ie$0$label_23#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    havoc inline$_v2.encode_ie$0$$result.question.3.$$static$;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(inline$_v2.encode_ie$0$p, inline$_v2.encode_ie$0$buf, 1, inline$_v2.encode_ie$0$$result.question.3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_29, inline$_v2.encode_ie$0$$result.question.3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_30, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_31, inline$_v2.encode_ie$0$buf);
    goto inline$_v2.encode_ie$0$label_24#2;

  inline$_v2.encode_ie$0$label_24#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 39} true;
    inline$_v2.encode_ie$0$result.encode_ie$1 := inline$_v2.encode_ie$0$$result.question.3.$$static$;
    assume _v2.value_is(_v2.__ctobpl_const_32, inline$_v2.encode_ie$0$$result.question.3.$$static$);
    goto inline$_v2.encode_ie$0$label_1#2;

  inline$_v2.encode_ie$0$label_16_true#2:
    assume _v2.INT_LT(2, inline$_v2.encode_ie$0$bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, inline$_v2.encode_ie$0$bufsize);
    goto inline$_v2.encode_ie$0$label_17#2;

  inline$_v2.encode_ie$0$label_17#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(inline$_v2.encode_ie$0$p, 0);
    _v2.OK := _v2.OK && _v2.Res_VALID_REGION(inline$_v2.encode_ie$0$p) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[inline$_v2.encode_ie$0$p := 120];
    assume _v2.value_is(_v2.__ctobpl_const_21, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_22, _v2.Mem_T.UCHAR[inline$_v2.encode_ie$0$p]);
    goto inline$_v2.encode_ie$0$label_18#2;

  inline$_v2.encode_ie$0$label_18#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(inline$_v2.encode_ie$0$p, 1, 1), 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(inline$_v2.encode_ie$0$p, 1, 1)) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v2.encode_ie$0$p, 1, 1) := 120];
    assume _v2.value_is(_v2.__ctobpl_const_23, inline$_v2.encode_ie$0$p);
    assume _v2.value_is(_v2.__ctobpl_const_24, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v2.encode_ie$0$p, 1, 1)]);
    goto inline$_v2.encode_ie$0$label_19#2;

  inline$_v2.encode_ie$0$label_19#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 33} true;
    inline$_v2.encode_ie$0$tempBoogie0 := _v2.INT_PLUS(inline$_v2.encode_ie$0$p, 1, 2);
    inline$_v2.encode_ie$0$p := inline$_v2.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_25, inline$_v2.encode_ie$0$p);
    goto inline$_v2.encode_ie$0$label_20#2;

  inline$_v2.encode_ie$0$label_20#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 34} true;
    havoc inline$_v2.encode_ie$0$tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(inline$_v2.encode_ie$0$bufsize, 2, 1, inline$_v2.encode_ie$0$tempBoogie0);
    inline$_v2.encode_ie$0$bufsize := inline$_v2.encode_ie$0$tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_26, inline$_v2.encode_ie$0$bufsize);
    goto inline$_v2.encode_ie$0$label_21#2;

  inline$_v2.encode_ie$0$label_21#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    assume _v2.value_is(_v2.__ctobpl_const_27, inline$_v2.encode_ie$0$i);
    inline$_v2.encode_ie$0$i := _v2.INT_PLUS(inline$_v2.encode_ie$0$i, 1, 1);
    goto inline$_v2.encode_ie$0$label_21_dummy#2;

  inline$_v2.encode_ie$0$label_21_dummy#2:
    assume false;
    goto inline$_v2.encode_ie$0$Return;

  inline$_v2.encode_ie$0$label_5_true#2:
    assume _v2.INT_LT(inline$_v2.encode_ie$0$bufsize, inline$_v2.encode_ie$0$leader_len);
    assume _v2.value_is(_v2.__ctobpl_const_1, inline$_v2.encode_ie$0$bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_2, inline$_v2.encode_ie$0$leader_len);
    goto inline$_v2.encode_ie$0$label_7#2;

  inline$_v2.encode_ie$0$label_7#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 14} true;
    inline$_v2.encode_ie$0$result.encode_ie$1 := 0;
    goto inline$_v2.encode_ie$0$label_1#2;

  inline$_v2.encode_ie$0$label_1#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 40} true;
    goto inline$_v2.encode_ie$0$Return;

  inline$_v2.encode_ie$0$Return:
    assume true;
    _v2.result.encode_ie$1 := inline$_v2.encode_ie$0$result.encode_ie$1;
    goto START$2;

  START$2:
    goto MS_L_0_1;

  MS_L_0_0:
    goto MS_L_taken_0, MS_L_not_taken_0;

  MS_L_taken_0:
    assume _v1.memcpy_1_done && _v2.memcpy_3_done;
    store__0__v1.OK, store__0__v1.Mem_T.UCHAR := _v1.OK, _v1.Mem_T.UCHAR;
    store__0__v2.OK, store__0__v2.Mem_T.UCHAR := _v2.OK, _v2.Mem_T.UCHAR;
    _v1.OK, _v1.Mem_T.UCHAR := _v1.memcpy_in_1_3, _v1.memcpy_in_1_4;
    _v2.OK, _v2.Mem_T.UCHAR := _v2.memcpy_in_3_3, _v2.memcpy_in_3_4;
    call out__v1.memcpy_out_1_0_0, out__v2.memcpy_out_3_0_0 := MS_Check__v1.memcpy___v2.memcpy(_v1.memcpy_in_1_0, _v1.memcpy_in_1_1, _v1.memcpy_in_1_2, _v2.memcpy_in_3_0, _v2.memcpy_in_3_1, _v2.memcpy_in_3_2);
    assume true;
    assume true;
    assume _v1.memcpy_out_1_0 == out__v1.memcpy_out_1_0_0
   && _v2.memcpy_out_3_0 == out__v2.memcpy_out_3_0_0;
    _v1.OK, _v1.Mem_T.UCHAR := store__0__v1.OK, store__0__v1.Mem_T.UCHAR;
    _v2.OK, _v2.Mem_T.UCHAR := store__0__v2.OK, store__0__v2.Mem_T.UCHAR;
    goto MS_L_meet_0;

  MS_L_not_taken_0:
    assume !(_v1.memcpy_1_done && _v2.memcpy_3_done);
    goto MS_L_meet_0;

  MS_L_meet_0:
    return;

  MS_L_0_1:
    goto MS_L_taken_1, MS_L_not_taken_1;

  MS_L_taken_1:
    assume _v1.encode_ie_loop_label_14_head_2_done
   && _v2.encode_ie_loop_label_14_head_4_done;
    store__1__v1.OK, store__1__v1.Mem_T.UCHAR := _v1.OK, _v1.Mem_T.UCHAR;
    store__1__v2.OK, store__1__v2.Mem_T.UCHAR := _v2.OK, _v2.Mem_T.UCHAR;
    _v1.OK, _v1.Mem_T.UCHAR := _v1.encode_ie_loop_label_14_head_in_2_5, _v1.encode_ie_loop_label_14_head_in_2_6;
    _v2.OK, _v2.Mem_T.UCHAR := _v2.encode_ie_loop_label_14_head_in_4_5, _v2.encode_ie_loop_label_14_head_in_4_6;
    call out__v1.encode_ie_loop_label_14_head_out_2_0_1, out__v1.encode_ie_loop_label_14_head_out_2_1_1, out__v1.encode_ie_loop_label_14_head_out_2_2_1, out__v2.encode_ie_loop_label_14_head_out_4_0_1, out__v2.encode_ie_loop_label_14_head_out_4_1_1, out__v2.encode_ie_loop_label_14_head_out_4_2_1, out__v2.encode_ie_loop_label_14_head_out_4_3_1 := MS_Check__v1.encode_ie_loop_label_14_head___v2.encode_ie_loop_label_14_head(_v1.encode_ie_loop_label_14_head_in_2_0, _v1.encode_ie_loop_label_14_head_in_2_1, _v1.encode_ie_loop_label_14_head_in_2_2, _v1.encode_ie_loop_label_14_head_in_2_3, _v1.encode_ie_loop_label_14_head_in_2_4, _v2.encode_ie_loop_label_14_head_in_4_0, _v2.encode_ie_loop_label_14_head_in_4_1, _v2.encode_ie_loop_label_14_head_in_4_2, _v2.encode_ie_loop_label_14_head_in_4_3, _v2.encode_ie_loop_label_14_head_in_4_4);
    assume _v1.Mem_T.UCHAR == _v1.encode_ie_loop_label_14_head_out_2_3
   && (_v1.OK <==> _v1.encode_ie_loop_label_14_head_out_2_4);
    assume _v2.Mem_T.UCHAR == _v2.encode_ie_loop_label_14_head_out_4_4
   && (_v2.OK <==> _v2.encode_ie_loop_label_14_head_out_4_5);
    assume _v1.encode_ie_loop_label_14_head_out_2_0
     == out__v1.encode_ie_loop_label_14_head_out_2_0_1
   && _v1.encode_ie_loop_label_14_head_out_2_1
     == out__v1.encode_ie_loop_label_14_head_out_2_1_1
   && _v1.encode_ie_loop_label_14_head_out_2_2
     == out__v1.encode_ie_loop_label_14_head_out_2_2_1
   && _v2.encode_ie_loop_label_14_head_out_4_0
     == out__v2.encode_ie_loop_label_14_head_out_4_0_1
   && _v2.encode_ie_loop_label_14_head_out_4_1
     == out__v2.encode_ie_loop_label_14_head_out_4_1_1
   && _v2.encode_ie_loop_label_14_head_out_4_2
     == out__v2.encode_ie_loop_label_14_head_out_4_2_1
   && _v2.encode_ie_loop_label_14_head_out_4_3
     == out__v2.encode_ie_loop_label_14_head_out_4_3_1;
    _v1.OK, _v1.Mem_T.UCHAR := store__1__v1.OK, store__1__v1.Mem_T.UCHAR;
    _v2.OK, _v2.Mem_T.UCHAR := store__1__v2.OK, store__1__v2.Mem_T.UCHAR;
    goto MS_L_meet_1;

  MS_L_not_taken_1:
    assume !(_v1.encode_ie_loop_label_14_head_2_done
   && _v2.encode_ie_loop_label_14_head_4_done);
    goto MS_L_meet_1;

  MS_L_meet_1:
    goto MS_L_0_0;
}



function {:inline true} MS$_v1.encode_ie_loop_label_14_head$_v2.encode_ie_loop_label_14_head(_v1.in_bufsize: int, 
    _v1.in_i: int, 
    _v1.in_ielen: int, 
    _v1.in_p: int, 
    _v1.in_tempBoogie0: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.Mem_T.UCHAR_: [int]int, 
    _v1.OK_: bool, 
    _v1.out_i: int, 
    _v1.out_p: int, 
    _v1.out_tempBoogie0: int, 
    _v2.in_bufsize: int, 
    _v2.in_i: int, 
    _v2.in_ielen: int, 
    _v2.in_p: int, 
    _v2.in_tempBoogie0: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.Mem_T.UCHAR_: [int]int, 
    _v2.OK_: bool, 
    _v2.out_bufsize: int, 
    _v2.out_i: int, 
    _v2.out_p: int, 
    _v2.out_tempBoogie0: int)
   : bool
{
  true
}

const {:existential true} _houdini_115: bool;

const {:existential true} _houdini_116: bool;

const {:existential true} _houdini_117: bool;

const {:existential true} _houdini_118: bool;

const {:existential true} _houdini_119: bool;

const {:existential true} _houdini_120: bool;

const {:existential true} _houdini_121: bool;

const {:existential true} _houdini_122: bool;

const {:existential true} _houdini_123: bool;

const {:existential true} _houdini_124: bool;

const {:existential true} _houdini_125: bool;

const {:existential true} _houdini_126: bool;

const {:existential true} _houdini_127: bool;

const {:existential true} _houdini_128: bool;

const {:existential true} _houdini_129: bool;

const {:existential true} _houdini_130: bool;

const {:existential true} _houdini_131: bool;

const {:existential true} _houdini_132: bool;

const {:existential true} _houdini_133: bool;

const {:existential true} _houdini_134: bool;

const {:existential true} _houdini_135: bool;

const {:existential true} _houdini_136: bool;

const {:existential true} _houdini_137: bool;

const {:existential true} _houdini_138: bool;

const {:existential true} _houdini_139: bool;

const {:existential true} _houdini_140: bool;

const {:existential true} _houdini_141: bool;

const {:existential true} _houdini_142: bool;

const {:existential true} _houdini_143: bool;

const {:existential true} _houdini_144: bool;

const {:existential true} _houdini_145: bool;

const {:existential true} _houdini_146: bool;

const {:existential true} _houdini_147: bool;

const {:existential true} _houdini_148: bool;

const {:existential true} _houdini_149: bool;

const {:existential true} _houdini_150: bool;

const {:existential true} _houdini_151: bool;

const {:existential true} _houdini_152: bool;

const {:existential true} _houdini_153: bool;

const {:existential true} _houdini_154: bool;

const {:existential true} _houdini_155: bool;

procedure MS_Check__v1.encode_ie_loop_label_14_head___v2.encode_ie_loop_label_14_head(_v1.in_bufsize: int, 
    _v1.in_i: int, 
    _v1.in_ielen: int, 
    _v1.in_p: int, 
    _v1.in_tempBoogie0: int, 
    _v2.in_bufsize: int, 
    _v2.in_i: int, 
    _v2.in_ielen: int, 
    _v2.in_p: int, 
    _v2.in_tempBoogie0: int)
   returns (_v1.out_i: int, 
    _v1.out_p: int, 
    _v1.out_tempBoogie0: int, 
    _v2.out_bufsize: int, 
    _v2.out_i: int, 
    _v2.out_p: int, 
    _v2.out_tempBoogie0: int);
  requires _houdini_124 ==> _v1.in_bufsize <= _v2.in_bufsize;
  requires _houdini_125 ==> _v2.in_bufsize <= _v1.in_bufsize;
  requires _houdini_126 ==> _v1.in_i <= _v2.in_i;
  requires _houdini_127 ==> _v2.in_i <= _v1.in_i;
  requires _houdini_128 ==> _v1.in_ielen <= _v2.in_ielen;
  requires _houdini_129 ==> _v2.in_ielen <= _v1.in_ielen;
  requires _houdini_130 ==> _v1.in_p <= _v2.in_p;
  requires _houdini_131 ==> _v2.in_p <= _v1.in_p;
  requires _houdini_132 ==> _v1.in_tempBoogie0 <= _v2.in_tempBoogie0;
  requires _houdini_133 ==> _v2.in_tempBoogie0 <= _v1.in_tempBoogie0;
  requires _houdini_134 ==> _v1.OK ==> _v2.OK;
  requires _houdini_135 ==> _v2.OK ==> _v1.OK;
  requires _houdini_136 ==> _v1.Mem == _v2.Mem;
  requires _houdini_137 ==> _v1.alloc <= _v2.alloc;
  requires _houdini_138 ==> _v2.alloc <= _v1.alloc;
  requires _houdini_139 ==> _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR;
  requires _houdini_140 ==> _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR;
  requires _houdini_141 ==> _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR;
  requires _houdini_142 ==> _v1.Mem_T.CHAR == _v2.Mem_T.CHAR;
  requires _houdini_143 ==> _v1.Mem_T.INT4 == _v2.Mem_T.INT4;
  requires _houdini_144 ==> _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR;
  requires _houdini_145 ==> _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR;
  requires _houdini_146 ==> _v1.Mem_T.PVOID == _v2.Mem_T.PVOID;
  requires _houdini_147
   ==> _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry;
  requires _houdini_148 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  requires _houdini_149 ==> _v1.Mem_T.VOID == _v2.Mem_T.VOID;
  requires _houdini_150
   ==> _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry;
  requires _houdini_151
   ==> _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
  requires _houdini_152 ==> _v1.detChoiceCnt <= _v2.detChoiceCnt;
  requires _houdini_153 ==> _v2.detChoiceCnt <= _v1.detChoiceCnt;
  requires _houdini_154 ==> _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE;
  requires _houdini_155 ==> _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.Mem_T.UCHAR, _v1.OK, _v2.Mem_T.UCHAR, _v2.OK;
  ensures MS$_v1.encode_ie_loop_label_14_head$_v2.encode_ie_loop_label_14_head(_v1.in_bufsize, 
  _v1.in_i, 
  _v1.in_ielen, 
  _v1.in_p, 
  _v1.in_tempBoogie0, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.Mem_T.UCHAR, 
  _v1.OK, 
  _v1.out_i, 
  _v1.out_p, 
  _v1.out_tempBoogie0, 
  _v2.in_bufsize, 
  _v2.in_i, 
  _v2.in_ielen, 
  _v2.in_p, 
  _v2.in_tempBoogie0, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.Mem_T.UCHAR, 
  _v2.OK, 
  _v2.out_bufsize, 
  _v2.out_i, 
  _v2.out_p, 
  _v2.out_tempBoogie0);
  ensures _houdini_115 ==> _v1.out_i <= _v2.out_i;
  ensures _houdini_116 ==> _v2.out_i <= _v1.out_i;
  ensures _houdini_117 ==> _v1.out_p <= _v2.out_p;
  ensures _houdini_118 ==> _v2.out_p <= _v1.out_p;
  ensures _houdini_119 ==> _v1.out_tempBoogie0 <= _v2.out_tempBoogie0;
  ensures _houdini_120 ==> _v2.out_tempBoogie0 <= _v1.out_tempBoogie0;
  ensures _houdini_121 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  ensures _houdini_122 ==> _v1.OK ==> _v2.OK;
  ensures _houdini_123 ==> _v2.OK ==> _v1.OK;



implementation MS_Check__v1.encode_ie_loop_label_14_head___v2.encode_ie_loop_label_14_head(_v1.in_bufsize: int, 
    _v1.in_i: int, 
    _v1.in_ielen: int, 
    _v1.in_p: int, 
    _v1.in_tempBoogie0: int, 
    _v2.in_bufsize: int, 
    _v2.in_i: int, 
    _v2.in_ielen: int, 
    _v2.in_p: int, 
    _v2.in_tempBoogie0: int)
   returns (_v1.out_i: int, 
    _v1.out_p: int, 
    _v1.out_tempBoogie0: int, 
    _v2.out_bufsize: int, 
    _v2.out_i: int, 
    _v2.out_p: int, 
    _v2.out_tempBoogie0: int)
{
  var inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$in_i: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$in_ielen: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$in_p: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$in_tempBoogie0: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$out_i: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$out_p: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0: int;
  var inline$_v1.encode_ie_loop_label_14_head$0$_v1.Mem_T.UCHAR: [int]int;
  var inline$_v1.encode_ie_loop_label_14_head$0$_v1.OK: bool;
  var inline$_v2.encode_ie_loop_label_14_head$0$in_bufsize: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$in_i: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$in_ielen: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$in_p: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$in_tempBoogie0: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$out_i: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$out_p: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0: int;
  var inline$_v2.encode_ie_loop_label_14_head$0$_v2.Mem_T.UCHAR: [int]int;
  var inline$_v2.encode_ie_loop_label_14_head$0$_v2.OK: bool;
  var _v1.encode_ie_loop_label_14_head_1_done: bool;
  var _v1.encode_ie_loop_label_14_head_in_1_0: int;
  var _v1.encode_ie_loop_label_14_head_in_1_1: int;
  var _v1.encode_ie_loop_label_14_head_in_1_2: int;
  var _v1.encode_ie_loop_label_14_head_in_1_3: int;
  var _v1.encode_ie_loop_label_14_head_in_1_4: int;
  var _v1.encode_ie_loop_label_14_head_in_1_5: [int]int;
  var _v1.encode_ie_loop_label_14_head_in_1_6: bool;
  var _v1.encode_ie_loop_label_14_head_out_1_0: int;
  var _v1.encode_ie_loop_label_14_head_out_1_1: int;
  var _v1.encode_ie_loop_label_14_head_out_1_2: int;
  var _v1.encode_ie_loop_label_14_head_out_1_3: [int]int;
  var _v1.encode_ie_loop_label_14_head_out_1_4: bool;
  var _v2.encode_ie_loop_label_14_head_2_done: bool;
  var _v2.encode_ie_loop_label_14_head_in_2_0: int;
  var _v2.encode_ie_loop_label_14_head_in_2_1: int;
  var _v2.encode_ie_loop_label_14_head_in_2_2: int;
  var _v2.encode_ie_loop_label_14_head_in_2_3: int;
  var _v2.encode_ie_loop_label_14_head_in_2_4: int;
  var _v2.encode_ie_loop_label_14_head_in_2_5: [int]int;
  var _v2.encode_ie_loop_label_14_head_in_2_6: bool;
  var _v2.encode_ie_loop_label_14_head_out_2_0: int;
  var _v2.encode_ie_loop_label_14_head_out_2_1: int;
  var _v2.encode_ie_loop_label_14_head_out_2_2: int;
  var _v2.encode_ie_loop_label_14_head_out_2_3: int;
  var _v2.encode_ie_loop_label_14_head_out_2_4: [int]int;
  var _v2.encode_ie_loop_label_14_head_out_2_5: bool;
  var store__0__v1.Mem_T.UCHAR: [int]int;
  var store__0__v1.OK: bool;
  var store__0__v2.Mem_T.UCHAR: [int]int;
  var store__0__v2.OK: bool;
  var out__v1.encode_ie_loop_label_14_head_out_1_0_0: int;
  var out__v1.encode_ie_loop_label_14_head_out_1_1_0: int;
  var out__v1.encode_ie_loop_label_14_head_out_1_2_0: int;
  var out__v2.encode_ie_loop_label_14_head_out_2_0_0: int;
  var out__v2.encode_ie_loop_label_14_head_out_2_1_0: int;
  var out__v2.encode_ie_loop_label_14_head_out_2_2_0: int;
  var out__v2.encode_ie_loop_label_14_head_out_2_3_0: int;

  START:
    _v1.encode_ie_loop_label_14_head_1_done, _v2.encode_ie_loop_label_14_head_2_done := false, false;
    goto inline$_v1.encode_ie_loop_label_14_head$0$Entry;

  inline$_v1.encode_ie_loop_label_14_head$0$Entry:
    inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize := _v1.in_bufsize;
    inline$_v1.encode_ie_loop_label_14_head$0$in_i := _v1.in_i;
    inline$_v1.encode_ie_loop_label_14_head$0$in_ielen := _v1.in_ielen;
    inline$_v1.encode_ie_loop_label_14_head$0$in_p := _v1.in_p;
    inline$_v1.encode_ie_loop_label_14_head$0$in_tempBoogie0 := _v1.in_tempBoogie0;
    havoc inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    inline$_v1.encode_ie_loop_label_14_head$0$_v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR;
    inline$_v1.encode_ie_loop_label_14_head$0$_v1.OK := _v1.OK;
    goto inline$_v1.encode_ie_loop_label_14_head$0$entry#2;

  inline$_v1.encode_ie_loop_label_14_head$0$entry#2:
    inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0 := inline$_v1.encode_ie_loop_label_14_head$0$in_i, inline$_v1.encode_ie_loop_label_14_head$0$in_p, inline$_v1.encode_ie_loop_label_14_head$0$in_tempBoogie0;
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_14_head#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_14_head#2:
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_14_true#2, inline$_v1.encode_ie_loop_label_14_head$0$label_14_false#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_14_false#2:
    assume !_v2.INT_LT(inline$_v1.encode_ie_loop_label_14_head$0$out_i, 
  inline$_v1.encode_ie_loop_label_14_head$0$in_ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, inline$_v1.encode_ie_loop_label_14_head$0$out_i);
    assume _v2.value_is(_v1.__ctobpl_const_17, inline$_v1.encode_ie_loop_label_14_head$0$in_ielen);
    inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0 := inline$_v1.encode_ie_loop_label_14_head$0$in_i, inline$_v1.encode_ie_loop_label_14_head$0$in_p, inline$_v1.encode_ie_loop_label_14_head$0$in_tempBoogie0;
    _v1.Mem_T.UCHAR := inline$_v1.encode_ie_loop_label_14_head$0$_v1.Mem_T.UCHAR;
    goto inline$_v1.encode_ie_loop_label_14_head$0$Return;

  inline$_v1.encode_ie_loop_label_14_head$0$label_14_true#2:
    assume _v2.INT_LT(inline$_v1.encode_ie_loop_label_14_head$0$out_i, 
  inline$_v1.encode_ie_loop_label_14_head$0$in_ielen);
    assume _v2.value_is(_v1.__ctobpl_const_16, inline$_v1.encode_ie_loop_label_14_head$0$out_i);
    assume _v2.value_is(_v1.__ctobpl_const_17, inline$_v1.encode_ie_loop_label_14_head$0$in_ielen);
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_16#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_16#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_16_true#2, inline$_v1.encode_ie_loop_label_14_head$0$label_16_false#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_16_false#2:
    assume !_v2.INT_LT(2, inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize);
    inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0 := inline$_v1.encode_ie_loop_label_14_head$0$in_i, inline$_v1.encode_ie_loop_label_14_head$0$in_p, inline$_v1.encode_ie_loop_label_14_head$0$in_tempBoogie0;
    _v1.Mem_T.UCHAR := inline$_v1.encode_ie_loop_label_14_head$0$_v1.Mem_T.UCHAR;
    goto inline$_v1.encode_ie_loop_label_14_head$0$Return;

  inline$_v1.encode_ie_loop_label_14_head$0$label_16_true#2:
    assume _v2.INT_LT(2, inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize);
    assume _v2.value_is(_v1.__ctobpl_const_20, inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize);
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_17#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_17#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(inline$_v1.encode_ie_loop_label_14_head$0$out_p, 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(inline$_v1.encode_ie_loop_label_14_head$0$out_p) == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[inline$_v1.encode_ie_loop_label_14_head$0$out_p := 120];
    assume _v2.value_is(_v1.__ctobpl_const_21, inline$_v1.encode_ie_loop_label_14_head$0$out_p);
    assume _v2.value_is(_v1.__ctobpl_const_22, 
  _v1.Mem_T.UCHAR[inline$_v1.encode_ie_loop_label_14_head$0$out_p]);
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_18#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_18#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(inline$_v1.encode_ie_loop_label_14_head$0$out_p, 1, 1), 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(inline$_v1.encode_ie_loop_label_14_head$0$out_p, 1, 1))
     == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v1.encode_ie_loop_label_14_head$0$out_p, 1, 1) := 120];
    assume _v2.value_is(_v1.__ctobpl_const_23, inline$_v1.encode_ie_loop_label_14_head$0$out_p);
    assume _v2.value_is(_v1.__ctobpl_const_24, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v1.encode_ie_loop_label_14_head$0$out_p, 1, 1)]);
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_19#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_19#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 33} true;
    inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0 := _v2.INT_PLUS(inline$_v1.encode_ie_loop_label_14_head$0$out_p, 1, 2);
    inline$_v1.encode_ie_loop_label_14_head$0$out_p := inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    assume _v2.value_is(_v1.__ctobpl_const_25, inline$_v1.encode_ie_loop_label_14_head$0$out_p);
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_20#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_20#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 20} true;
    assume _v2.value_is(_v1.__ctobpl_const_26, inline$_v1.encode_ie_loop_label_14_head$0$out_i);
    inline$_v1.encode_ie_loop_label_14_head$0$out_i := _v2.INT_PLUS(inline$_v1.encode_ie_loop_label_14_head$0$out_i, 1, 1);
    goto inline$_v1.encode_ie_loop_label_14_head$0$label_20_dummy#2;

  inline$_v1.encode_ie_loop_label_14_head$0$label_20_dummy#2:
    _v1.encode_ie_loop_label_14_head_in_1_0, _v1.encode_ie_loop_label_14_head_in_1_1, _v1.encode_ie_loop_label_14_head_in_1_2, _v1.encode_ie_loop_label_14_head_in_1_3, _v1.encode_ie_loop_label_14_head_in_1_4, _v1.encode_ie_loop_label_14_head_in_1_5, _v1.encode_ie_loop_label_14_head_in_1_6 := inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize, inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$in_ielen, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0, _v1.Mem_T.UCHAR, _v1.OK;
    call inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0 := _v1.encode_ie_loop_label_14_head(inline$_v1.encode_ie_loop_label_14_head$0$in_bufsize, inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$in_ielen, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0);
    _v1.encode_ie_loop_label_14_head_1_done := true;
    _v1.encode_ie_loop_label_14_head_out_1_0, _v1.encode_ie_loop_label_14_head_out_1_1, _v1.encode_ie_loop_label_14_head_out_1_2, _v1.encode_ie_loop_label_14_head_out_1_3, _v1.encode_ie_loop_label_14_head_out_1_4 := inline$_v1.encode_ie_loop_label_14_head$0$out_i, inline$_v1.encode_ie_loop_label_14_head$0$out_p, inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0, _v1.Mem_T.UCHAR, _v1.OK;
    goto inline$_v1.encode_ie_loop_label_14_head$0$Return;

  inline$_v1.encode_ie_loop_label_14_head$0$Return:
    assume true;
    _v1.out_i := inline$_v1.encode_ie_loop_label_14_head$0$out_i;
    _v1.out_p := inline$_v1.encode_ie_loop_label_14_head$0$out_p;
    _v1.out_tempBoogie0 := inline$_v1.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    goto START$1;

  START$1:
    goto inline$_v2.encode_ie_loop_label_14_head$0$Entry;

  inline$_v2.encode_ie_loop_label_14_head$0$Entry:
    inline$_v2.encode_ie_loop_label_14_head$0$in_bufsize := _v2.in_bufsize;
    inline$_v2.encode_ie_loop_label_14_head$0$in_i := _v2.in_i;
    inline$_v2.encode_ie_loop_label_14_head$0$in_ielen := _v2.in_ielen;
    inline$_v2.encode_ie_loop_label_14_head$0$in_p := _v2.in_p;
    inline$_v2.encode_ie_loop_label_14_head$0$in_tempBoogie0 := _v2.in_tempBoogie0;
    havoc inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    inline$_v2.encode_ie_loop_label_14_head$0$_v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR;
    inline$_v2.encode_ie_loop_label_14_head$0$_v2.OK := _v2.OK;
    goto inline$_v2.encode_ie_loop_label_14_head$0$entry#2;

  inline$_v2.encode_ie_loop_label_14_head$0$entry#2:
    inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0 := inline$_v2.encode_ie_loop_label_14_head$0$in_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$in_i, inline$_v2.encode_ie_loop_label_14_head$0$in_p, inline$_v2.encode_ie_loop_label_14_head$0$in_tempBoogie0;
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_14_head#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_14_head#2:
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_14_true#2, inline$_v2.encode_ie_loop_label_14_head$0$label_14_false#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_14_false#2:
    assume !_v2.INT_LT(inline$_v2.encode_ie_loop_label_14_head$0$out_i, 
  inline$_v2.encode_ie_loop_label_14_head$0$in_ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, inline$_v2.encode_ie_loop_label_14_head$0$out_i);
    assume _v2.value_is(_v2.__ctobpl_const_17, inline$_v2.encode_ie_loop_label_14_head$0$in_ielen);
    inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0 := inline$_v2.encode_ie_loop_label_14_head$0$in_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$in_i, inline$_v2.encode_ie_loop_label_14_head$0$in_p, inline$_v2.encode_ie_loop_label_14_head$0$in_tempBoogie0;
    _v2.Mem_T.UCHAR := inline$_v2.encode_ie_loop_label_14_head$0$_v2.Mem_T.UCHAR;
    goto inline$_v2.encode_ie_loop_label_14_head$0$Return;

  inline$_v2.encode_ie_loop_label_14_head$0$label_14_true#2:
    assume _v2.INT_LT(inline$_v2.encode_ie_loop_label_14_head$0$out_i, 
  inline$_v2.encode_ie_loop_label_14_head$0$in_ielen);
    assume _v2.value_is(_v2.__ctobpl_const_16, inline$_v2.encode_ie_loop_label_14_head$0$out_i);
    assume _v2.value_is(_v2.__ctobpl_const_17, inline$_v2.encode_ie_loop_label_14_head$0$in_ielen);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_16#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_16#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_16_true#2, inline$_v2.encode_ie_loop_label_14_head$0$label_16_false#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_16_false#2:
    assume !_v2.INT_LT(2, inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize);
    inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0 := inline$_v2.encode_ie_loop_label_14_head$0$in_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$in_i, inline$_v2.encode_ie_loop_label_14_head$0$in_p, inline$_v2.encode_ie_loop_label_14_head$0$in_tempBoogie0;
    _v2.Mem_T.UCHAR := inline$_v2.encode_ie_loop_label_14_head$0$_v2.Mem_T.UCHAR;
    goto inline$_v2.encode_ie_loop_label_14_head$0$Return;

  inline$_v2.encode_ie_loop_label_14_head$0$label_16_true#2:
    assume _v2.INT_LT(2, inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize);
    assume _v2.value_is(_v2.__ctobpl_const_20, inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_17#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_17#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 30} true;
    assume _v2.INT_GEQ(inline$_v2.encode_ie_loop_label_14_head$0$out_p, 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(inline$_v2.encode_ie_loop_label_14_head$0$out_p) == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[inline$_v2.encode_ie_loop_label_14_head$0$out_p := 120];
    assume _v2.value_is(_v2.__ctobpl_const_21, inline$_v2.encode_ie_loop_label_14_head$0$out_p);
    assume _v2.value_is(_v2.__ctobpl_const_22, 
  _v2.Mem_T.UCHAR[inline$_v2.encode_ie_loop_label_14_head$0$out_p]);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_18#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_18#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 32} true;
    assume _v2.INT_GEQ(_v2.INT_PLUS(inline$_v2.encode_ie_loop_label_14_head$0$out_p, 1, 1), 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(inline$_v2.encode_ie_loop_label_14_head$0$out_p, 1, 1))
     == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v2.encode_ie_loop_label_14_head$0$out_p, 1, 1) := 120];
    assume _v2.value_is(_v2.__ctobpl_const_23, inline$_v2.encode_ie_loop_label_14_head$0$out_p);
    assume _v2.value_is(_v2.__ctobpl_const_24, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(inline$_v2.encode_ie_loop_label_14_head$0$out_p, 1, 1)]);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_19#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_19#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 33} true;
    inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0 := _v2.INT_PLUS(inline$_v2.encode_ie_loop_label_14_head$0$out_p, 1, 2);
    inline$_v2.encode_ie_loop_label_14_head$0$out_p := inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_25, inline$_v2.encode_ie_loop_label_14_head$0$out_p);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_20#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_20#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 34} true;
    havoc inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    assume _v2.INT_MINUS_BOTH_PTR_OR_BOTH_INT(inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, 2, 1, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0);
    inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize := inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    assume _v2.value_is(_v2.__ctobpl_const_26, inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_21#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_21#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 20} true;
    assume _v2.value_is(_v2.__ctobpl_const_27, inline$_v2.encode_ie_loop_label_14_head$0$out_i);
    inline$_v2.encode_ie_loop_label_14_head$0$out_i := _v2.INT_PLUS(inline$_v2.encode_ie_loop_label_14_head$0$out_i, 1, 1);
    goto inline$_v2.encode_ie_loop_label_14_head$0$label_21_dummy#2;

  inline$_v2.encode_ie_loop_label_14_head$0$label_21_dummy#2:
    _v2.encode_ie_loop_label_14_head_in_2_0, _v2.encode_ie_loop_label_14_head_in_2_1, _v2.encode_ie_loop_label_14_head_in_2_2, _v2.encode_ie_loop_label_14_head_in_2_3, _v2.encode_ie_loop_label_14_head_in_2_4, _v2.encode_ie_loop_label_14_head_in_2_5, _v2.encode_ie_loop_label_14_head_in_2_6 := inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$in_ielen, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0, _v2.Mem_T.UCHAR, _v2.OK;
    call inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0 := _v2.encode_ie_loop_label_14_head(inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$in_ielen, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0);
    _v2.encode_ie_loop_label_14_head_2_done := true;
    _v2.encode_ie_loop_label_14_head_out_2_0, _v2.encode_ie_loop_label_14_head_out_2_1, _v2.encode_ie_loop_label_14_head_out_2_2, _v2.encode_ie_loop_label_14_head_out_2_3, _v2.encode_ie_loop_label_14_head_out_2_4, _v2.encode_ie_loop_label_14_head_out_2_5 := inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize, inline$_v2.encode_ie_loop_label_14_head$0$out_i, inline$_v2.encode_ie_loop_label_14_head$0$out_p, inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0, _v2.Mem_T.UCHAR, _v2.OK;
    goto inline$_v2.encode_ie_loop_label_14_head$0$Return;

  inline$_v2.encode_ie_loop_label_14_head$0$Return:
    assume true;
    _v2.out_bufsize := inline$_v2.encode_ie_loop_label_14_head$0$out_bufsize;
    _v2.out_i := inline$_v2.encode_ie_loop_label_14_head$0$out_i;
    _v2.out_p := inline$_v2.encode_ie_loop_label_14_head$0$out_p;
    _v2.out_tempBoogie0 := inline$_v2.encode_ie_loop_label_14_head$0$out_tempBoogie0;
    goto START$2;

  START$2:
    goto MS_L_0_0;

  MS_L_0_0:
    goto MS_L_taken_0, MS_L_not_taken_0;

  MS_L_taken_0:
    assume _v1.encode_ie_loop_label_14_head_1_done
   && _v2.encode_ie_loop_label_14_head_2_done;
    store__0__v1.Mem_T.UCHAR, store__0__v1.OK := _v1.Mem_T.UCHAR, _v1.OK;
    store__0__v2.Mem_T.UCHAR, store__0__v2.OK := _v2.Mem_T.UCHAR, _v2.OK;
    _v1.Mem_T.UCHAR, _v1.OK := _v1.encode_ie_loop_label_14_head_in_1_5, _v1.encode_ie_loop_label_14_head_in_1_6;
    _v2.Mem_T.UCHAR, _v2.OK := _v2.encode_ie_loop_label_14_head_in_2_5, _v2.encode_ie_loop_label_14_head_in_2_6;
    call out__v1.encode_ie_loop_label_14_head_out_1_0_0, out__v1.encode_ie_loop_label_14_head_out_1_1_0, out__v1.encode_ie_loop_label_14_head_out_1_2_0, out__v2.encode_ie_loop_label_14_head_out_2_0_0, out__v2.encode_ie_loop_label_14_head_out_2_1_0, out__v2.encode_ie_loop_label_14_head_out_2_2_0, out__v2.encode_ie_loop_label_14_head_out_2_3_0 := MS_Check__v1.encode_ie_loop_label_14_head___v2.encode_ie_loop_label_14_head(_v1.encode_ie_loop_label_14_head_in_1_0, _v1.encode_ie_loop_label_14_head_in_1_1, _v1.encode_ie_loop_label_14_head_in_1_2, _v1.encode_ie_loop_label_14_head_in_1_3, _v1.encode_ie_loop_label_14_head_in_1_4, _v2.encode_ie_loop_label_14_head_in_2_0, _v2.encode_ie_loop_label_14_head_in_2_1, _v2.encode_ie_loop_label_14_head_in_2_2, _v2.encode_ie_loop_label_14_head_in_2_3, _v2.encode_ie_loop_label_14_head_in_2_4);
    assume _v1.Mem_T.UCHAR == _v1.encode_ie_loop_label_14_head_out_1_3
   && (_v1.OK <==> _v1.encode_ie_loop_label_14_head_out_1_4);
    assume _v2.Mem_T.UCHAR == _v2.encode_ie_loop_label_14_head_out_2_4
   && (_v2.OK <==> _v2.encode_ie_loop_label_14_head_out_2_5);
    assume _v1.encode_ie_loop_label_14_head_out_1_0
     == out__v1.encode_ie_loop_label_14_head_out_1_0_0
   && _v1.encode_ie_loop_label_14_head_out_1_1
     == out__v1.encode_ie_loop_label_14_head_out_1_1_0
   && _v1.encode_ie_loop_label_14_head_out_1_2
     == out__v1.encode_ie_loop_label_14_head_out_1_2_0
   && _v2.encode_ie_loop_label_14_head_out_2_0
     == out__v2.encode_ie_loop_label_14_head_out_2_0_0
   && _v2.encode_ie_loop_label_14_head_out_2_1
     == out__v2.encode_ie_loop_label_14_head_out_2_1_0
   && _v2.encode_ie_loop_label_14_head_out_2_2
     == out__v2.encode_ie_loop_label_14_head_out_2_2_0
   && _v2.encode_ie_loop_label_14_head_out_2_3
     == out__v2.encode_ie_loop_label_14_head_out_2_3_0;
    _v1.Mem_T.UCHAR, _v1.OK := store__0__v1.Mem_T.UCHAR, store__0__v1.OK;
    _v2.Mem_T.UCHAR, _v2.OK := store__0__v2.Mem_T.UCHAR, store__0__v2.OK;
    goto MS_L_meet_0;

  MS_L_not_taken_0:
    assume !(_v1.encode_ie_loop_label_14_head_1_done
   && _v2.encode_ie_loop_label_14_head_2_done);
    goto MS_L_meet_0;

  MS_L_meet_0:
    return;
}



function {:inline true} MS$_v1.giwscan_cb$_v2.giwscan_cb(_v1.se_.1: int, 
    _v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.alloc_: int, 
    _v1.OK_: bool, 
    _v1.Mem_T.UCHAR_: [int]int, 
    _v1.result.giwscan_cb$1: int, 
    _v2.se_.1: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.alloc_: int, 
    _v2.OK_: bool, 
    _v2.Mem_T.UCHAR_: [int]int, 
    _v2.result.giwscan_cb$1: int)
   : bool
{
  true
}

const {:existential true} _houdini_156: bool;

const {:existential true} _houdini_157: bool;

const {:existential true} _houdini_158: bool;

const {:existential true} _houdini_159: bool;

const {:existential true} _houdini_160: bool;

const {:existential true} _houdini_161: bool;

const {:existential true} _houdini_162: bool;

const {:existential true} _houdini_163: bool;

const {:existential true} _houdini_164: bool;

const {:existential true} _houdini_165: bool;

const {:existential true} _houdini_166: bool;

const {:existential true} _houdini_167: bool;

const {:existential true} _houdini_168: bool;

const {:existential true} _houdini_169: bool;

const {:existential true} _houdini_170: bool;

const {:existential true} _houdini_171: bool;

const {:existential true} _houdini_172: bool;

const {:existential true} _houdini_173: bool;

const {:existential true} _houdini_174: bool;

const {:existential true} _houdini_175: bool;

const {:existential true} _houdini_176: bool;

const {:existential true} _houdini_177: bool;

const {:existential true} _houdini_178: bool;

const {:existential true} _houdini_179: bool;

const {:existential true} _houdini_180: bool;

const {:existential true} _houdini_181: bool;

const {:existential true} _houdini_182: bool;

const {:existential true} _houdini_183: bool;

const {:existential true} _houdini_184: bool;

const {:existential true} _houdini_185: bool;

const {:existential true} _houdini_186: bool;

procedure MS_Check__v1.giwscan_cb___v2.giwscan_cb(_v1.se_.1: int, _v2.se_.1: int)
   returns (_v1.result.giwscan_cb$1: int, _v2.result.giwscan_cb$1: int);
  requires _houdini_163 ==> _v1.se_.1 <= _v2.se_.1;
  requires _houdini_164 ==> _v2.se_.1 <= _v1.se_.1;
  requires _houdini_165 ==> _v1.OK ==> _v2.OK;
  requires _houdini_166 ==> _v2.OK ==> _v1.OK;
  requires _houdini_167 ==> _v1.Mem == _v2.Mem;
  requires _houdini_168 ==> _v1.alloc <= _v2.alloc;
  requires _houdini_169 ==> _v2.alloc <= _v1.alloc;
  requires _houdini_170 ==> _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR;
  requires _houdini_171 ==> _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR;
  requires _houdini_172 ==> _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR;
  requires _houdini_173 ==> _v1.Mem_T.CHAR == _v2.Mem_T.CHAR;
  requires _houdini_174 ==> _v1.Mem_T.INT4 == _v2.Mem_T.INT4;
  requires _houdini_175 ==> _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR;
  requires _houdini_176 ==> _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR;
  requires _houdini_177 ==> _v1.Mem_T.PVOID == _v2.Mem_T.PVOID;
  requires _houdini_178
   ==> _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry;
  requires _houdini_179 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;
  requires _houdini_180 ==> _v1.Mem_T.VOID == _v2.Mem_T.VOID;
  requires _houdini_181
   ==> _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry;
  requires _houdini_182
   ==> _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
  requires _houdini_183 ==> _v1.detChoiceCnt <= _v2.detChoiceCnt;
  requires _houdini_184 ==> _v2.detChoiceCnt <= _v1.detChoiceCnt;
  requires _houdini_185 ==> _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE;
  requires _houdini_186 ==> _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
  ensures MS$_v1.giwscan_cb$_v2.giwscan_cb(_v1.se_.1, 
  old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.alloc, 
  _v1.OK, 
  _v1.Mem_T.UCHAR, 
  _v1.result.giwscan_cb$1, 
  _v2.se_.1, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.alloc, 
  _v2.OK, 
  _v2.Mem_T.UCHAR, 
  _v2.result.giwscan_cb$1);
  ensures _houdini_156 ==> _v1.result.giwscan_cb$1 <= _v2.result.giwscan_cb$1;
  ensures _houdini_157 ==> _v2.result.giwscan_cb$1 <= _v1.result.giwscan_cb$1;
  ensures _houdini_158 ==> _v1.alloc <= _v2.alloc;
  ensures _houdini_159 ==> _v2.alloc <= _v1.alloc;
  ensures _houdini_160 ==> _v1.OK ==> _v2.OK;
  ensures _houdini_161 ==> _v2.OK ==> _v1.OK;
  ensures _houdini_162 ==> _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR;



implementation MS_Check__v1.giwscan_cb___v2.giwscan_cb(_v1.se_.1: int, _v2.se_.1: int)
   returns (_v1.result.giwscan_cb$1: int, _v2.result.giwscan_cb$1: int)
{
  var inline$_v1.giwscan_cb$0$havoc_stringTemp: int;
  var inline$_v1.giwscan_cb$0$condVal: int;
  var inline$_v1.giwscan_cb$0$buf: int;
  var inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$: int;
  var inline$_v1.giwscan_cb$0$result.encode_ie$2: int;
  var inline$_v1.giwscan_cb$0$rsn_leader: int;
  var inline$_v1.giwscan_cb$0$se: int;
  var inline$_v1.giwscan_cb$0$tempBoogie0: int;
  var inline$_v1.giwscan_cb$0$tempBoogie1: int;
  var inline$_v1.giwscan_cb$0$tempBoogie2: int;
  var inline$_v1.giwscan_cb$0$tempBoogie3: int;
  var inline$_v1.giwscan_cb$0$tempBoogie4: int;
  var inline$_v1.giwscan_cb$0$tempBoogie5: int;
  var inline$_v1.giwscan_cb$0$tempBoogie6: int;
  var inline$_v1.giwscan_cb$0$tempBoogie7: int;
  var inline$_v1.giwscan_cb$0$tempBoogie8: int;
  var inline$_v1.giwscan_cb$0$tempBoogie9: int;
  var inline$_v1.giwscan_cb$0$tempBoogie10: int;
  var inline$_v1.giwscan_cb$0$tempBoogie11: int;
  var inline$_v1.giwscan_cb$0$tempBoogie12: int;
  var inline$_v1.giwscan_cb$0$tempBoogie13: int;
  var inline$_v1.giwscan_cb$0$tempBoogie14: int;
  var inline$_v1.giwscan_cb$0$tempBoogie15: int;
  var inline$_v1.giwscan_cb$0$tempBoogie16: int;
  var inline$_v1.giwscan_cb$0$tempBoogie17: int;
  var inline$_v1.giwscan_cb$0$tempBoogie18: int;
  var inline$_v1.giwscan_cb$0$tempBoogie19: int;
  var inline$_v1.giwscan_cb$0$__havoc_dummy_return: int;
  var inline$_v1.giwscan_cb$0$se_.1: int;
  var inline$_v1.giwscan_cb$0$result.giwscan_cb$1: int;
  var inline$_v1.giwscan_cb$0$_v1.alloc: int;
  var inline$_v1.giwscan_cb$0$_v1.OK: bool;
  var inline$_v1.giwscan_cb$0$_v1.Mem_T.UCHAR: [int]int;
  var inline$_v2.giwscan_cb$0$havoc_stringTemp: int;
  var inline$_v2.giwscan_cb$0$condVal: int;
  var inline$_v2.giwscan_cb$0$buf: int;
  var inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$: int;
  var inline$_v2.giwscan_cb$0$result.encode_ie$2: int;
  var inline$_v2.giwscan_cb$0$rsn_leader: int;
  var inline$_v2.giwscan_cb$0$se: int;
  var inline$_v2.giwscan_cb$0$tempBoogie0: int;
  var inline$_v2.giwscan_cb$0$tempBoogie1: int;
  var inline$_v2.giwscan_cb$0$tempBoogie2: int;
  var inline$_v2.giwscan_cb$0$tempBoogie3: int;
  var inline$_v2.giwscan_cb$0$tempBoogie4: int;
  var inline$_v2.giwscan_cb$0$tempBoogie5: int;
  var inline$_v2.giwscan_cb$0$tempBoogie6: int;
  var inline$_v2.giwscan_cb$0$tempBoogie7: int;
  var inline$_v2.giwscan_cb$0$tempBoogie8: int;
  var inline$_v2.giwscan_cb$0$tempBoogie9: int;
  var inline$_v2.giwscan_cb$0$tempBoogie10: int;
  var inline$_v2.giwscan_cb$0$tempBoogie11: int;
  var inline$_v2.giwscan_cb$0$tempBoogie12: int;
  var inline$_v2.giwscan_cb$0$tempBoogie13: int;
  var inline$_v2.giwscan_cb$0$tempBoogie14: int;
  var inline$_v2.giwscan_cb$0$tempBoogie15: int;
  var inline$_v2.giwscan_cb$0$tempBoogie16: int;
  var inline$_v2.giwscan_cb$0$tempBoogie17: int;
  var inline$_v2.giwscan_cb$0$tempBoogie18: int;
  var inline$_v2.giwscan_cb$0$tempBoogie19: int;
  var inline$_v2.giwscan_cb$0$__havoc_dummy_return: int;
  var inline$_v2.giwscan_cb$0$se_.1: int;
  var inline$_v2.giwscan_cb$0$result.giwscan_cb$1: int;
  var inline$_v2.giwscan_cb$0$_v2.alloc: int;
  var inline$_v2.giwscan_cb$0$_v2.OK: bool;
  var inline$_v2.giwscan_cb$0$_v2.Mem_T.UCHAR: [int]int;
  var _v1.__HAVOC_det_malloc_1_done: bool;
  var _v1.__HAVOC_det_malloc_in_1_0: int;
  var _v1.__HAVOC_det_malloc_in_1_1: int;
  var _v1.__HAVOC_det_malloc_in_1_2: bool;
  var _v1.__HAVOC_det_malloc_in_1_3: [int]int;
  var _v1.__HAVOC_det_malloc_out_1_0: int;
  var _v1.__HAVOC_det_malloc_out_1_1: int;
  var _v1.__HAVOC_det_malloc_2_done: bool;
  var _v1.__HAVOC_det_malloc_in_2_0: int;
  var _v1.__HAVOC_det_malloc_in_2_1: int;
  var _v1.__HAVOC_det_malloc_in_2_2: bool;
  var _v1.__HAVOC_det_malloc_in_2_3: [int]int;
  var _v1.__HAVOC_det_malloc_out_2_0: int;
  var _v1.__HAVOC_det_malloc_out_2_1: int;
  var _v1.encode_ie_3_done: bool;
  var _v1.encode_ie_in_3_0: int;
  var _v1.encode_ie_in_3_1: int;
  var _v1.encode_ie_in_3_2: int;
  var _v1.encode_ie_in_3_3: int;
  var _v1.encode_ie_in_3_4: int;
  var _v1.encode_ie_in_3_5: int;
  var _v1.encode_ie_in_3_6: int;
  var _v1.encode_ie_in_3_7: bool;
  var _v1.encode_ie_in_3_8: [int]int;
  var _v1.encode_ie_out_3_0: int;
  var _v1.encode_ie_out_3_1: bool;
  var _v1.encode_ie_out_3_2: [int]int;
  var _v1.__HAVOC_free_4_done: bool;
  var _v1.__HAVOC_free_in_4_0: int;
  var _v1.__HAVOC_free_in_4_1: int;
  var _v1.__HAVOC_free_in_4_2: bool;
  var _v1.__HAVOC_free_in_4_3: [int]int;
  var _v1.__HAVOC_free_5_done: bool;
  var _v1.__HAVOC_free_in_5_0: int;
  var _v1.__HAVOC_free_in_5_1: int;
  var _v1.__HAVOC_free_in_5_2: bool;
  var _v1.__HAVOC_free_in_5_3: [int]int;
  var _v2.__HAVOC_det_malloc_6_done: bool;
  var _v2.__HAVOC_det_malloc_in_6_0: int;
  var _v2.__HAVOC_det_malloc_in_6_1: int;
  var _v2.__HAVOC_det_malloc_in_6_2: bool;
  var _v2.__HAVOC_det_malloc_in_6_3: [int]int;
  var _v2.__HAVOC_det_malloc_out_6_0: int;
  var _v2.__HAVOC_det_malloc_out_6_1: int;
  var _v2.__HAVOC_det_malloc_7_done: bool;
  var _v2.__HAVOC_det_malloc_in_7_0: int;
  var _v2.__HAVOC_det_malloc_in_7_1: int;
  var _v2.__HAVOC_det_malloc_in_7_2: bool;
  var _v2.__HAVOC_det_malloc_in_7_3: [int]int;
  var _v2.__HAVOC_det_malloc_out_7_0: int;
  var _v2.__HAVOC_det_malloc_out_7_1: int;
  var _v2.encode_ie_8_done: bool;
  var _v2.encode_ie_in_8_0: int;
  var _v2.encode_ie_in_8_1: int;
  var _v2.encode_ie_in_8_2: int;
  var _v2.encode_ie_in_8_3: int;
  var _v2.encode_ie_in_8_4: int;
  var _v2.encode_ie_in_8_5: int;
  var _v2.encode_ie_in_8_6: int;
  var _v2.encode_ie_in_8_7: bool;
  var _v2.encode_ie_in_8_8: [int]int;
  var _v2.encode_ie_out_8_0: int;
  var _v2.encode_ie_out_8_1: bool;
  var _v2.encode_ie_out_8_2: [int]int;
  var _v2.__HAVOC_free_9_done: bool;
  var _v2.__HAVOC_free_in_9_0: int;
  var _v2.__HAVOC_free_in_9_1: int;
  var _v2.__HAVOC_free_in_9_2: bool;
  var _v2.__HAVOC_free_in_9_3: [int]int;
  var _v2.__HAVOC_free_10_done: bool;
  var _v2.__HAVOC_free_in_10_0: int;
  var _v2.__HAVOC_free_in_10_1: int;
  var _v2.__HAVOC_free_in_10_2: bool;
  var _v2.__HAVOC_free_in_10_3: [int]int;
  var store__0__v1.alloc: int;
  var store__0__v1.OK: bool;
  var store__0__v1.Mem_T.UCHAR: [int]int;
  var store__0__v2.alloc: int;
  var store__0__v2.OK: bool;
  var store__0__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_1_0_0: int;
  var out__v2.__HAVOC_det_malloc_out_6_0_0: int;
  var store__1__v1.alloc: int;
  var store__1__v1.OK: bool;
  var store__1__v1.Mem_T.UCHAR: [int]int;
  var store__1__v2.alloc: int;
  var store__1__v2.OK: bool;
  var store__1__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_1_0_1: int;
  var out__v2.__HAVOC_det_malloc_out_7_0_1: int;
  var store__2__v1.alloc: int;
  var store__2__v1.OK: bool;
  var store__2__v1.Mem_T.UCHAR: [int]int;
  var store__2__v2.alloc: int;
  var store__2__v2.OK: bool;
  var store__2__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_2_0_2: int;
  var out__v2.__HAVOC_det_malloc_out_6_0_2: int;
  var store__3__v1.alloc: int;
  var store__3__v1.OK: bool;
  var store__3__v1.Mem_T.UCHAR: [int]int;
  var store__3__v2.alloc: int;
  var store__3__v2.OK: bool;
  var store__3__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_2_0_3: int;
  var out__v2.__HAVOC_det_malloc_out_7_0_3: int;
  var store__4__v1.alloc: int;
  var store__4__v1.OK: bool;
  var store__4__v1.Mem_T.UCHAR: [int]int;
  var store__4__v2.alloc: int;
  var store__4__v2.OK: bool;
  var store__4__v2.Mem_T.UCHAR: [int]int;
  var out__v1.encode_ie_out_3_0_4: int;
  var out__v2.encode_ie_out_8_0_4: int;
  var store__5__v1.alloc: int;
  var store__5__v1.OK: bool;
  var store__5__v1.Mem_T.UCHAR: [int]int;
  var store__5__v2.alloc: int;
  var store__5__v2.OK: bool;
  var store__5__v2.Mem_T.UCHAR: [int]int;
  var store__6__v1.alloc: int;
  var store__6__v1.OK: bool;
  var store__6__v1.Mem_T.UCHAR: [int]int;
  var store__6__v2.alloc: int;
  var store__6__v2.OK: bool;
  var store__6__v2.Mem_T.UCHAR: [int]int;
  var store__7__v1.alloc: int;
  var store__7__v1.OK: bool;
  var store__7__v1.Mem_T.UCHAR: [int]int;
  var store__7__v2.alloc: int;
  var store__7__v2.OK: bool;
  var store__7__v2.Mem_T.UCHAR: [int]int;
  var store__8__v1.alloc: int;
  var store__8__v1.OK: bool;
  var store__8__v1.Mem_T.UCHAR: [int]int;
  var store__8__v2.alloc: int;
  var store__8__v2.OK: bool;
  var store__8__v2.Mem_T.UCHAR: [int]int;

  START:
    _v1.__HAVOC_det_malloc_1_done, _v1.__HAVOC_det_malloc_2_done, _v1.encode_ie_3_done, _v1.__HAVOC_free_4_done, _v1.__HAVOC_free_5_done, _v2.__HAVOC_det_malloc_6_done, _v2.__HAVOC_det_malloc_7_done, _v2.encode_ie_8_done, _v2.__HAVOC_free_9_done, _v2.__HAVOC_free_10_done := false, false, false, false, false, false, false, false, false, false;
    goto inline$_v1.giwscan_cb$0$Entry;

  inline$_v1.giwscan_cb$0$Entry:
    inline$_v1.giwscan_cb$0$se_.1 := _v1.se_.1;
    havoc inline$_v1.giwscan_cb$0$havoc_stringTemp, inline$_v1.giwscan_cb$0$condVal, inline$_v1.giwscan_cb$0$buf, inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$, inline$_v1.giwscan_cb$0$result.encode_ie$2, inline$_v1.giwscan_cb$0$rsn_leader, inline$_v1.giwscan_cb$0$se, inline$_v1.giwscan_cb$0$tempBoogie0, inline$_v1.giwscan_cb$0$tempBoogie1, inline$_v1.giwscan_cb$0$tempBoogie2, inline$_v1.giwscan_cb$0$tempBoogie3, inline$_v1.giwscan_cb$0$tempBoogie4, inline$_v1.giwscan_cb$0$tempBoogie5, inline$_v1.giwscan_cb$0$tempBoogie6, inline$_v1.giwscan_cb$0$tempBoogie7, inline$_v1.giwscan_cb$0$tempBoogie8, inline$_v1.giwscan_cb$0$tempBoogie9, inline$_v1.giwscan_cb$0$tempBoogie10, inline$_v1.giwscan_cb$0$tempBoogie11, inline$_v1.giwscan_cb$0$tempBoogie12, inline$_v1.giwscan_cb$0$tempBoogie13, inline$_v1.giwscan_cb$0$tempBoogie14, inline$_v1.giwscan_cb$0$tempBoogie15, inline$_v1.giwscan_cb$0$tempBoogie16, inline$_v1.giwscan_cb$0$tempBoogie17, inline$_v1.giwscan_cb$0$tempBoogie18, inline$_v1.giwscan_cb$0$tempBoogie19, inline$_v1.giwscan_cb$0$__havoc_dummy_return, inline$_v1.giwscan_cb$0$result.giwscan_cb$1;
    inline$_v1.giwscan_cb$0$_v1.alloc := _v1.alloc;
    inline$_v1.giwscan_cb$0$_v1.OK := _v1.OK;
    inline$_v1.giwscan_cb$0$_v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR;
    goto inline$_v1.giwscan_cb$0$anon0#2;

  inline$_v1.giwscan_cb$0$anon0#2:
    inline$_v1.giwscan_cb$0$havoc_stringTemp := 0;
    goto inline$_v1.giwscan_cb$0$start#2;

  inline$_v1.giwscan_cb$0$start#2:
    assume _v2.INT_LT(inline$_v1.giwscan_cb$0$se_.1, _v1.alloc);
    _v1.__HAVOC_det_malloc_in_1_0, _v1.__HAVOC_det_malloc_in_1_1, _v1.__HAVOC_det_malloc_in_1_2, _v1.__HAVOC_det_malloc_in_1_3 := 6, _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    call inline$_v1.giwscan_cb$0$buf := _v1.__HAVOC_det_malloc(6);
    _v1.__HAVOC_det_malloc_1_done := true;
    _v1.__HAVOC_det_malloc_out_1_0, _v1.__HAVOC_det_malloc_out_1_1 := inline$_v1.giwscan_cb$0$buf, _v1.alloc;
    inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$ := 0;
    inline$_v1.giwscan_cb$0$result.encode_ie$2 := 0;
    inline$_v1.giwscan_cb$0$result.giwscan_cb$1 := 0;
    _v1.__HAVOC_det_malloc_in_2_0, _v1.__HAVOC_det_malloc_in_2_1, _v1.__HAVOC_det_malloc_in_2_2, _v1.__HAVOC_det_malloc_in_2_3 := 1, _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    call inline$_v1.giwscan_cb$0$rsn_leader := _v1.__HAVOC_det_malloc(1);
    _v1.__HAVOC_det_malloc_2_done := true;
    _v1.__HAVOC_det_malloc_out_2_0, _v1.__HAVOC_det_malloc_out_2_1 := inline$_v1.giwscan_cb$0$rsn_leader, _v1.alloc;
    inline$_v1.giwscan_cb$0$se := 0;
    assume _v2.INT_GEQ(inline$_v1.giwscan_cb$0$se_.1, 0);
    inline$_v1.giwscan_cb$0$se := inline$_v1.giwscan_cb$0$se_.1;
    goto inline$_v1.giwscan_cb$0$label_3#2;

  inline$_v1.giwscan_cb$0$label_3#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 45} true;
    goto inline$_v1.giwscan_cb$0$label_4#2;

  inline$_v1.giwscan_cb$0$label_4#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 46} true;
    goto inline$_v1.giwscan_cb$0$label_5#2;

  inline$_v1.giwscan_cb$0$label_5#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 50} true;
    assume _v2.INT_GEQ(inline$_v1.giwscan_cb$0$se, 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se))
     == 1;
    assert true;
    goto inline$_v1.giwscan_cb$0$label_5_true#2, inline$_v1.giwscan_cb$0$label_5_false#2;

  inline$_v1.giwscan_cb$0$label_5_false#2:
    assume _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]
   == 0;
    assume _v2.value_is(_v1.__ctobpl_const_32, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_33, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    goto inline$_v1.giwscan_cb$0$label_6#2;

  inline$_v1.giwscan_cb$0$label_5_true#2:
    assume _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]
   != 0;
    assume _v2.value_is(_v1.__ctobpl_const_32, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_33, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    goto inline$_v1.giwscan_cb$0$label_7#2;

  inline$_v1.giwscan_cb$0$label_7#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 51} true;
    assume _v2.INT_GEQ(inline$_v1.giwscan_cb$0$se, 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
        1, 
        0))
     == 1;
    assert true;
    goto inline$_v1.giwscan_cb$0$label_7_true#2, inline$_v1.giwscan_cb$0$label_7_false#2;

  inline$_v1.giwscan_cb$0$label_7_false#2:
    assume !_v2.INT_EQ(_v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v1.__ctobpl_const_34, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_35, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_36, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
    1, 
    0)]);
    goto inline$_v1.giwscan_cb$0$label_6#2;

  inline$_v1.giwscan_cb$0$label_7_true#2:
    assume _v2.INT_EQ(_v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v1.__ctobpl_const_34, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_35, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_36, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
    1, 
    0)]);
    goto inline$_v1.giwscan_cb$0$label_8#2;

  inline$_v1.giwscan_cb$0$label_8#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 53} true;
    assume _v2.INT_GEQ(inline$_v1.giwscan_cb$0$se, 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
        1, 
        1))
     == 1;
    assert true;
    inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$ := _v2.INT_PLUS(_v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
    1, 
    1)], 
  1, 
  2);
    assume _v2.value_is(_v1.__ctobpl_const_37, inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_38, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_39, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_40, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], 
    1, 
    1)]);
    goto inline$_v1.giwscan_cb$0$label_9#2;

  inline$_v1.giwscan_cb$0$label_9#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 52} true;
    assume _v2.INT_GEQ(inline$_v1.giwscan_cb$0$se, 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(inline$_v1.giwscan_cb$0$se, 0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se))
     == 1;
    assert true;
    _v1.encode_ie_in_3_0, _v1.encode_ie_in_3_1, _v1.encode_ie_in_3_2, _v1.encode_ie_in_3_3, _v1.encode_ie_in_3_4, _v1.encode_ie_in_3_5, _v1.encode_ie_in_3_6, _v1.encode_ie_in_3_7, _v1.encode_ie_in_3_8 := inline$_v1.giwscan_cb$0$buf, 6, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$, inline$_v1.giwscan_cb$0$rsn_leader, 1, _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    call inline$_v1.giwscan_cb$0$result.encode_ie$2 := _v1.encode_ie(inline$_v1.giwscan_cb$0$buf, 6, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)], inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$, inline$_v1.giwscan_cb$0$rsn_leader, 1);
    _v1.encode_ie_3_done := true;
    _v1.encode_ie_out_3_0, _v1.encode_ie_out_3_1, _v1.encode_ie_out_3_2 := inline$_v1.giwscan_cb$0$result.encode_ie$2, _v1.OK, _v1.Mem_T.UCHAR;
    assume _v2.value_is(_v1.__ctobpl_const_41, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_42, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_43, inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v1.__ctobpl_const_44, inline$_v1.giwscan_cb$0$se);
    assume _v2.value_is(_v1.__ctobpl_const_45, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.giwscan_cb$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_46, inline$_v1.giwscan_cb$0$$encode_ie.arg.4$3.$$static$);
    goto inline$_v1.giwscan_cb$0$label_6#2;

  inline$_v1.giwscan_cb$0$label_6#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 57} true;
    inline$_v1.giwscan_cb$0$result.giwscan_cb$1 := 0;
    goto inline$_v1.giwscan_cb$0$label_1#2;

  inline$_v1.giwscan_cb$0$label_1#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 58} true;
    _v1.__HAVOC_free_in_4_0, _v1.__HAVOC_free_in_4_1, _v1.__HAVOC_free_in_4_2, _v1.__HAVOC_free_in_4_3 := inline$_v1.giwscan_cb$0$buf, _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    call _v1.__HAVOC_free(inline$_v1.giwscan_cb$0$buf);
    _v1.__HAVOC_free_4_done := true;
    _v1.__HAVOC_free_in_5_0, _v1.__HAVOC_free_in_5_1, _v1.__HAVOC_free_in_5_2, _v1.__HAVOC_free_in_5_3 := inline$_v1.giwscan_cb$0$rsn_leader, _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    call _v1.__HAVOC_free(inline$_v1.giwscan_cb$0$rsn_leader);
    _v1.__HAVOC_free_5_done := true;
    goto inline$_v1.giwscan_cb$0$Return;

  inline$_v1.giwscan_cb$0$Return:
    assume true;
    _v1.result.giwscan_cb$1 := inline$_v1.giwscan_cb$0$result.giwscan_cb$1;
    goto START$1;

  START$1:
    goto inline$_v2.giwscan_cb$0$Entry;

  inline$_v2.giwscan_cb$0$Entry:
    inline$_v2.giwscan_cb$0$se_.1 := _v2.se_.1;
    havoc inline$_v2.giwscan_cb$0$havoc_stringTemp, inline$_v2.giwscan_cb$0$condVal, inline$_v2.giwscan_cb$0$buf, inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$, inline$_v2.giwscan_cb$0$result.encode_ie$2, inline$_v2.giwscan_cb$0$rsn_leader, inline$_v2.giwscan_cb$0$se, inline$_v2.giwscan_cb$0$tempBoogie0, inline$_v2.giwscan_cb$0$tempBoogie1, inline$_v2.giwscan_cb$0$tempBoogie2, inline$_v2.giwscan_cb$0$tempBoogie3, inline$_v2.giwscan_cb$0$tempBoogie4, inline$_v2.giwscan_cb$0$tempBoogie5, inline$_v2.giwscan_cb$0$tempBoogie6, inline$_v2.giwscan_cb$0$tempBoogie7, inline$_v2.giwscan_cb$0$tempBoogie8, inline$_v2.giwscan_cb$0$tempBoogie9, inline$_v2.giwscan_cb$0$tempBoogie10, inline$_v2.giwscan_cb$0$tempBoogie11, inline$_v2.giwscan_cb$0$tempBoogie12, inline$_v2.giwscan_cb$0$tempBoogie13, inline$_v2.giwscan_cb$0$tempBoogie14, inline$_v2.giwscan_cb$0$tempBoogie15, inline$_v2.giwscan_cb$0$tempBoogie16, inline$_v2.giwscan_cb$0$tempBoogie17, inline$_v2.giwscan_cb$0$tempBoogie18, inline$_v2.giwscan_cb$0$tempBoogie19, inline$_v2.giwscan_cb$0$__havoc_dummy_return, inline$_v2.giwscan_cb$0$result.giwscan_cb$1;
    inline$_v2.giwscan_cb$0$_v2.alloc := _v2.alloc;
    inline$_v2.giwscan_cb$0$_v2.OK := _v2.OK;
    inline$_v2.giwscan_cb$0$_v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR;
    goto inline$_v2.giwscan_cb$0$anon0#2;

  inline$_v2.giwscan_cb$0$anon0#2:
    inline$_v2.giwscan_cb$0$havoc_stringTemp := 0;
    goto inline$_v2.giwscan_cb$0$start#2;

  inline$_v2.giwscan_cb$0$start#2:
    assume _v2.INT_LT(inline$_v2.giwscan_cb$0$se_.1, _v2.alloc);
    _v2.__HAVOC_det_malloc_in_6_0, _v2.__HAVOC_det_malloc_in_6_1, _v2.__HAVOC_det_malloc_in_6_2, _v2.__HAVOC_det_malloc_in_6_3 := 6, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    call inline$_v2.giwscan_cb$0$buf := _v2.__HAVOC_det_malloc(6);
    _v2.__HAVOC_det_malloc_6_done := true;
    _v2.__HAVOC_det_malloc_out_6_0, _v2.__HAVOC_det_malloc_out_6_1 := inline$_v2.giwscan_cb$0$buf, _v2.alloc;
    inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$ := 0;
    inline$_v2.giwscan_cb$0$result.encode_ie$2 := 0;
    inline$_v2.giwscan_cb$0$result.giwscan_cb$1 := 0;
    _v2.__HAVOC_det_malloc_in_7_0, _v2.__HAVOC_det_malloc_in_7_1, _v2.__HAVOC_det_malloc_in_7_2, _v2.__HAVOC_det_malloc_in_7_3 := 1, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    call inline$_v2.giwscan_cb$0$rsn_leader := _v2.__HAVOC_det_malloc(1);
    _v2.__HAVOC_det_malloc_7_done := true;
    _v2.__HAVOC_det_malloc_out_7_0, _v2.__HAVOC_det_malloc_out_7_1 := inline$_v2.giwscan_cb$0$rsn_leader, _v2.alloc;
    inline$_v2.giwscan_cb$0$se := 0;
    assume _v2.INT_GEQ(inline$_v2.giwscan_cb$0$se_.1, 0);
    inline$_v2.giwscan_cb$0$se := inline$_v2.giwscan_cb$0$se_.1;
    goto inline$_v2.giwscan_cb$0$label_3#2;

  inline$_v2.giwscan_cb$0$label_3#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 46} true;
    goto inline$_v2.giwscan_cb$0$label_4#2;

  inline$_v2.giwscan_cb$0$label_4#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 47} true;
    goto inline$_v2.giwscan_cb$0$label_5#2;

  inline$_v2.giwscan_cb$0$label_5#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 51} true;
    assume _v2.INT_GEQ(inline$_v2.giwscan_cb$0$se, 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se))
     == 1;
    assert true;
    goto inline$_v2.giwscan_cb$0$label_5_true#2, inline$_v2.giwscan_cb$0$label_5_false#2;

  inline$_v2.giwscan_cb$0$label_5_false#2:
    assume _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]
   == 0;
    assume _v2.value_is(_v2.__ctobpl_const_33, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_34, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    goto inline$_v2.giwscan_cb$0$label_6#2;

  inline$_v2.giwscan_cb$0$label_5_true#2:
    assume _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]
   != 0;
    assume _v2.value_is(_v2.__ctobpl_const_33, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_34, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    goto inline$_v2.giwscan_cb$0$label_7#2;

  inline$_v2.giwscan_cb$0$label_7#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 52} true;
    assume _v2.INT_GEQ(inline$_v2.giwscan_cb$0$se, 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
        1, 
        0))
     == 1;
    assert true;
    goto inline$_v2.giwscan_cb$0$label_7_true#2, inline$_v2.giwscan_cb$0$label_7_false#2;

  inline$_v2.giwscan_cb$0$label_7_false#2:
    assume !_v2.INT_EQ(_v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v2.__ctobpl_const_35, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_36, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_37, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
    1, 
    0)]);
    goto inline$_v2.giwscan_cb$0$label_6#2;

  inline$_v2.giwscan_cb$0$label_7_true#2:
    assume _v2.INT_EQ(_v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
    1, 
    0)], 
  200);
    assume _v2.value_is(_v2.__ctobpl_const_35, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_36, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_37, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
    1, 
    0)]);
    goto inline$_v2.giwscan_cb$0$label_8#2;

  inline$_v2.giwscan_cb$0$label_8#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 54} true;
    assume _v2.INT_GEQ(inline$_v2.giwscan_cb$0$se, 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
        1, 
        1))
     == 1;
    assert true;
    inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$ := _v2.INT_PLUS(_v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
    1, 
    1)], 
  1, 
  2);
    assume _v2.value_is(_v2.__ctobpl_const_38, inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_39, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_40, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_41, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], 
    1, 
    1)]);
    goto inline$_v2.giwscan_cb$0$label_9#2;

  inline$_v2.giwscan_cb$0$label_9#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 53} true;
    assume _v2.INT_GEQ(inline$_v2.giwscan_cb$0$se, 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(inline$_v2.giwscan_cb$0$se, 0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se))
     == 1;
    assert true;
    _v2.encode_ie_in_8_0, _v2.encode_ie_in_8_1, _v2.encode_ie_in_8_2, _v2.encode_ie_in_8_3, _v2.encode_ie_in_8_4, _v2.encode_ie_in_8_5, _v2.encode_ie_in_8_6, _v2.encode_ie_in_8_7, _v2.encode_ie_in_8_8 := inline$_v2.giwscan_cb$0$buf, 6, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$, inline$_v2.giwscan_cb$0$rsn_leader, 1, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    call inline$_v2.giwscan_cb$0$result.encode_ie$2 := _v2.encode_ie(inline$_v2.giwscan_cb$0$buf, 6, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)], inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$, inline$_v2.giwscan_cb$0$rsn_leader, 1);
    _v2.encode_ie_8_done := true;
    _v2.encode_ie_out_8_0, _v2.encode_ie_out_8_1, _v2.encode_ie_out_8_2 := inline$_v2.giwscan_cb$0$result.encode_ie$2, _v2.OK, _v2.Mem_T.UCHAR;
    assume _v2.value_is(_v2.__ctobpl_const_42, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_43, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_44, inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$);
    assume _v2.value_is(_v2.__ctobpl_const_45, inline$_v2.giwscan_cb$0$se);
    assume _v2.value_is(_v2.__ctobpl_const_46, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.giwscan_cb$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_47, inline$_v2.giwscan_cb$0$$encode_ie.arg.4$3.$$static$);
    goto inline$_v2.giwscan_cb$0$label_6#2;

  inline$_v2.giwscan_cb$0$label_6#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 58} true;
    inline$_v2.giwscan_cb$0$result.giwscan_cb$1 := 0;
    goto inline$_v2.giwscan_cb$0$label_1#2;

  inline$_v2.giwscan_cb$0$label_1#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 59} true;
    _v2.__HAVOC_free_in_9_0, _v2.__HAVOC_free_in_9_1, _v2.__HAVOC_free_in_9_2, _v2.__HAVOC_free_in_9_3 := inline$_v2.giwscan_cb$0$buf, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    call _v2.__HAVOC_free(inline$_v2.giwscan_cb$0$buf);
    _v2.__HAVOC_free_9_done := true;
    _v2.__HAVOC_free_in_10_0, _v2.__HAVOC_free_in_10_1, _v2.__HAVOC_free_in_10_2, _v2.__HAVOC_free_in_10_3 := inline$_v2.giwscan_cb$0$rsn_leader, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    call _v2.__HAVOC_free(inline$_v2.giwscan_cb$0$rsn_leader);
    _v2.__HAVOC_free_10_done := true;
    goto inline$_v2.giwscan_cb$0$Return;

  inline$_v2.giwscan_cb$0$Return:
    assume true;
    _v2.result.giwscan_cb$1 := inline$_v2.giwscan_cb$0$result.giwscan_cb$1;
    goto START$2;

  START$2:
    goto MS_L_0_8;

  MS_L_0_0:
    goto MS_L_taken_0, MS_L_not_taken_0;

  MS_L_taken_0:
    assume _v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_6_done;
    store__0__v1.alloc, store__0__v1.OK, store__0__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__0__v2.alloc, store__0__v2.OK, store__0__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_1_1, _v1.__HAVOC_det_malloc_in_1_2, _v1.__HAVOC_det_malloc_in_1_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_6_1, _v2.__HAVOC_det_malloc_in_6_2, _v2.__HAVOC_det_malloc_in_6_3;
    call out__v1.__HAVOC_det_malloc_out_1_0_0, out__v2.__HAVOC_det_malloc_out_6_0_0 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_1_0, _v2.__HAVOC_det_malloc_in_6_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_1_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_6_1;
    assume _v1.__HAVOC_det_malloc_out_1_0 == out__v1.__HAVOC_det_malloc_out_1_0_0
   && _v2.__HAVOC_det_malloc_out_6_0 == out__v2.__HAVOC_det_malloc_out_6_0_0;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__0__v1.alloc, store__0__v1.OK, store__0__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__0__v2.alloc, store__0__v2.OK, store__0__v2.Mem_T.UCHAR;
    goto MS_L_meet_0;

  MS_L_not_taken_0:
    assume !(_v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_6_done);
    goto MS_L_meet_0;

  MS_L_meet_0:
    return;

  MS_L_0_1:
    goto MS_L_taken_1, MS_L_not_taken_1;

  MS_L_taken_1:
    assume _v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_7_done;
    store__1__v1.alloc, store__1__v1.OK, store__1__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__1__v2.alloc, store__1__v2.OK, store__1__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_1_1, _v1.__HAVOC_det_malloc_in_1_2, _v1.__HAVOC_det_malloc_in_1_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_7_1, _v2.__HAVOC_det_malloc_in_7_2, _v2.__HAVOC_det_malloc_in_7_3;
    call out__v1.__HAVOC_det_malloc_out_1_0_1, out__v2.__HAVOC_det_malloc_out_7_0_1 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_1_0, _v2.__HAVOC_det_malloc_in_7_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_1_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_7_1;
    assume _v1.__HAVOC_det_malloc_out_1_0 == out__v1.__HAVOC_det_malloc_out_1_0_1
   && _v2.__HAVOC_det_malloc_out_7_0 == out__v2.__HAVOC_det_malloc_out_7_0_1;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__1__v1.alloc, store__1__v1.OK, store__1__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__1__v2.alloc, store__1__v2.OK, store__1__v2.Mem_T.UCHAR;
    goto MS_L_meet_1;

  MS_L_not_taken_1:
    assume !(_v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_7_done);
    goto MS_L_meet_1;

  MS_L_meet_1:
    goto MS_L_0_0;

  MS_L_0_2:
    goto MS_L_taken_2, MS_L_not_taken_2;

  MS_L_taken_2:
    assume _v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_6_done;
    store__2__v1.alloc, store__2__v1.OK, store__2__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__2__v2.alloc, store__2__v2.OK, store__2__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_2_1, _v1.__HAVOC_det_malloc_in_2_2, _v1.__HAVOC_det_malloc_in_2_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_6_1, _v2.__HAVOC_det_malloc_in_6_2, _v2.__HAVOC_det_malloc_in_6_3;
    call out__v1.__HAVOC_det_malloc_out_2_0_2, out__v2.__HAVOC_det_malloc_out_6_0_2 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_2_0, _v2.__HAVOC_det_malloc_in_6_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_2_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_6_1;
    assume _v1.__HAVOC_det_malloc_out_2_0 == out__v1.__HAVOC_det_malloc_out_2_0_2
   && _v2.__HAVOC_det_malloc_out_6_0 == out__v2.__HAVOC_det_malloc_out_6_0_2;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__2__v1.alloc, store__2__v1.OK, store__2__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__2__v2.alloc, store__2__v2.OK, store__2__v2.Mem_T.UCHAR;
    goto MS_L_meet_2;

  MS_L_not_taken_2:
    assume !(_v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_6_done);
    goto MS_L_meet_2;

  MS_L_meet_2:
    goto MS_L_0_1;

  MS_L_0_3:
    goto MS_L_taken_3, MS_L_not_taken_3;

  MS_L_taken_3:
    assume _v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_7_done;
    store__3__v1.alloc, store__3__v1.OK, store__3__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__3__v2.alloc, store__3__v2.OK, store__3__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_2_1, _v1.__HAVOC_det_malloc_in_2_2, _v1.__HAVOC_det_malloc_in_2_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_7_1, _v2.__HAVOC_det_malloc_in_7_2, _v2.__HAVOC_det_malloc_in_7_3;
    call out__v1.__HAVOC_det_malloc_out_2_0_3, out__v2.__HAVOC_det_malloc_out_7_0_3 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_2_0, _v2.__HAVOC_det_malloc_in_7_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_2_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_7_1;
    assume _v1.__HAVOC_det_malloc_out_2_0 == out__v1.__HAVOC_det_malloc_out_2_0_3
   && _v2.__HAVOC_det_malloc_out_7_0 == out__v2.__HAVOC_det_malloc_out_7_0_3;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__3__v1.alloc, store__3__v1.OK, store__3__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__3__v2.alloc, store__3__v2.OK, store__3__v2.Mem_T.UCHAR;
    goto MS_L_meet_3;

  MS_L_not_taken_3:
    assume !(_v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_7_done);
    goto MS_L_meet_3;

  MS_L_meet_3:
    goto MS_L_0_2;

  MS_L_0_4:
    goto MS_L_taken_4, MS_L_not_taken_4;

  MS_L_taken_4:
    assume _v1.encode_ie_3_done && _v2.encode_ie_8_done;
    store__4__v1.alloc, store__4__v1.OK, store__4__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__4__v2.alloc, store__4__v2.OK, store__4__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.encode_ie_in_3_6, _v1.encode_ie_in_3_7, _v1.encode_ie_in_3_8;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.encode_ie_in_8_6, _v2.encode_ie_in_8_7, _v2.encode_ie_in_8_8;
    call out__v1.encode_ie_out_3_0_4, out__v2.encode_ie_out_8_0_4 := MS_Check__v1.encode_ie___v2.encode_ie(_v1.encode_ie_in_3_0, _v1.encode_ie_in_3_1, _v1.encode_ie_in_3_2, _v1.encode_ie_in_3_3, _v1.encode_ie_in_3_4, _v1.encode_ie_in_3_5, _v2.encode_ie_in_8_0, _v2.encode_ie_in_8_1, _v2.encode_ie_in_8_2, _v2.encode_ie_in_8_3, _v2.encode_ie_in_8_4, _v2.encode_ie_in_8_5);
    assume (_v1.OK <==> _v1.encode_ie_out_3_1) && _v1.Mem_T.UCHAR == _v1.encode_ie_out_3_2;
    assume (_v2.OK <==> _v2.encode_ie_out_8_1) && _v2.Mem_T.UCHAR == _v2.encode_ie_out_8_2;
    assume _v1.encode_ie_out_3_0 == out__v1.encode_ie_out_3_0_4
   && _v2.encode_ie_out_8_0 == out__v2.encode_ie_out_8_0_4;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__4__v1.alloc, store__4__v1.OK, store__4__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__4__v2.alloc, store__4__v2.OK, store__4__v2.Mem_T.UCHAR;
    goto MS_L_meet_4;

  MS_L_not_taken_4:
    assume !(_v1.encode_ie_3_done && _v2.encode_ie_8_done);
    goto MS_L_meet_4;

  MS_L_meet_4:
    goto MS_L_0_3;

  MS_L_0_5:
    goto MS_L_taken_5, MS_L_not_taken_5;

  MS_L_taken_5:
    assume _v1.__HAVOC_free_4_done && _v2.__HAVOC_free_9_done;
    store__5__v1.alloc, store__5__v1.OK, store__5__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__5__v2.alloc, store__5__v2.OK, store__5__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_4_1, _v1.__HAVOC_free_in_4_2, _v1.__HAVOC_free_in_4_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_9_1, _v2.__HAVOC_free_in_9_2, _v2.__HAVOC_free_in_9_3;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_4_0, _v2.__HAVOC_free_in_9_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__5__v1.alloc, store__5__v1.OK, store__5__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__5__v2.alloc, store__5__v2.OK, store__5__v2.Mem_T.UCHAR;
    goto MS_L_meet_5;

  MS_L_not_taken_5:
    assume !(_v1.__HAVOC_free_4_done && _v2.__HAVOC_free_9_done);
    goto MS_L_meet_5;

  MS_L_meet_5:
    goto MS_L_0_4;

  MS_L_0_6:
    goto MS_L_taken_6, MS_L_not_taken_6;

  MS_L_taken_6:
    assume _v1.__HAVOC_free_4_done && _v2.__HAVOC_free_10_done;
    store__6__v1.alloc, store__6__v1.OK, store__6__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__6__v2.alloc, store__6__v2.OK, store__6__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_4_1, _v1.__HAVOC_free_in_4_2, _v1.__HAVOC_free_in_4_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_10_1, _v2.__HAVOC_free_in_10_2, _v2.__HAVOC_free_in_10_3;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_4_0, _v2.__HAVOC_free_in_10_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__6__v1.alloc, store__6__v1.OK, store__6__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__6__v2.alloc, store__6__v2.OK, store__6__v2.Mem_T.UCHAR;
    goto MS_L_meet_6;

  MS_L_not_taken_6:
    assume !(_v1.__HAVOC_free_4_done && _v2.__HAVOC_free_10_done);
    goto MS_L_meet_6;

  MS_L_meet_6:
    goto MS_L_0_5;

  MS_L_0_7:
    goto MS_L_taken_7, MS_L_not_taken_7;

  MS_L_taken_7:
    assume _v1.__HAVOC_free_5_done && _v2.__HAVOC_free_9_done;
    store__7__v1.alloc, store__7__v1.OK, store__7__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__7__v2.alloc, store__7__v2.OK, store__7__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_5_1, _v1.__HAVOC_free_in_5_2, _v1.__HAVOC_free_in_5_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_9_1, _v2.__HAVOC_free_in_9_2, _v2.__HAVOC_free_in_9_3;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_5_0, _v2.__HAVOC_free_in_9_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__7__v1.alloc, store__7__v1.OK, store__7__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__7__v2.alloc, store__7__v2.OK, store__7__v2.Mem_T.UCHAR;
    goto MS_L_meet_7;

  MS_L_not_taken_7:
    assume !(_v1.__HAVOC_free_5_done && _v2.__HAVOC_free_9_done);
    goto MS_L_meet_7;

  MS_L_meet_7:
    goto MS_L_0_6;

  MS_L_0_8:
    goto MS_L_taken_8, MS_L_not_taken_8;

  MS_L_taken_8:
    assume _v1.__HAVOC_free_5_done && _v2.__HAVOC_free_10_done;
    store__8__v1.alloc, store__8__v1.OK, store__8__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    store__8__v2.alloc, store__8__v2.OK, store__8__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_5_1, _v1.__HAVOC_free_in_5_2, _v1.__HAVOC_free_in_5_3;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_10_1, _v2.__HAVOC_free_in_10_2, _v2.__HAVOC_free_in_10_3;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_5_0, _v2.__HAVOC_free_in_10_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR := store__8__v1.alloc, store__8__v1.OK, store__8__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR := store__8__v2.alloc, store__8__v2.OK, store__8__v2.Mem_T.UCHAR;
    goto MS_L_meet_8;

  MS_L_not_taken_8:
    assume !(_v1.__HAVOC_free_5_done && _v2.__HAVOC_free_10_done);
    goto MS_L_meet_8;

  MS_L_meet_8:
    goto MS_L_0_7;
}



function {:inline true} MS$_v1.main$_v2.main(_v1.OK_old: bool, 
    _v1.Mem_old: [name][int]int, 
    _v1.alloc_old: int, 
    _v1.Mem_T.A1CHAR_old: [int]int, 
    _v1.Mem_T.A5UCHAR_old: [int]int, 
    _v1.Mem_T.A6UCHAR_old: [int]int, 
    _v1.Mem_T.CHAR_old: [int]int, 
    _v1.Mem_T.INT4_old: [int]int, 
    _v1.Mem_T.PCHAR_old: [int]int, 
    _v1.Mem_T.PUCHAR_old: [int]int, 
    _v1.Mem_T.PVOID_old: [int]int, 
    _v1.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.UCHAR_old: [int]int, 
    _v1.Mem_T.VOID_old: [int]int, 
    _v1.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v1.detChoiceCnt_old: int, 
    _v1.Res_KERNEL_SOURCE_old: [int]int, 
    _v1.Res_PROBED_old: [int]int, 
    _v1.alloc_: int, 
    _v1.OK_: bool, 
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry_: [int]int, 
    _v1.Mem_T.UCHAR_: [int]int, 
    _v1.result.main$1: int, 
    _v2.OK_old: bool, 
    _v2.Mem_old: [name][int]int, 
    _v2.alloc_old: int, 
    _v2.Mem_T.A1CHAR_old: [int]int, 
    _v2.Mem_T.A5UCHAR_old: [int]int, 
    _v2.Mem_T.A6UCHAR_old: [int]int, 
    _v2.Mem_T.CHAR_old: [int]int, 
    _v2.Mem_T.INT4_old: [int]int, 
    _v2.Mem_T.PCHAR_old: [int]int, 
    _v2.Mem_T.PUCHAR_old: [int]int, 
    _v2.Mem_T.PVOID_old: [int]int, 
    _v2.Mem_T.Pieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.UCHAR_old: [int]int, 
    _v2.Mem_T.VOID_old: [int]int, 
    _v2.Mem_T.ieee80211_scan_entry_old: [int]int, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_old: [int]int, 
    _v2.detChoiceCnt_old: int, 
    _v2.Res_KERNEL_SOURCE_old: [int]int, 
    _v2.Res_PROBED_old: [int]int, 
    _v2.alloc_: int, 
    _v2.OK_: bool, 
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry_: [int]int, 
    _v2.Mem_T.UCHAR_: [int]int, 
    _v2.result.main$1: int)
   : bool
{
  true
}

procedure MS_Check__v1.main___v2.main() returns (_v1.result.main$1: int, _v2.result.main$1: int);
  requires (_v1.OK <==> _v2.OK)
   && _v1.Mem == _v2.Mem
   && _v1.alloc == _v2.alloc
   && _v1.Mem_T.A1CHAR == _v2.Mem_T.A1CHAR
   && _v1.Mem_T.A5UCHAR == _v2.Mem_T.A5UCHAR
   && _v1.Mem_T.A6UCHAR == _v2.Mem_T.A6UCHAR
   && _v1.Mem_T.CHAR == _v2.Mem_T.CHAR
   && _v1.Mem_T.INT4 == _v2.Mem_T.INT4
   && _v1.Mem_T.PCHAR == _v2.Mem_T.PCHAR
   && _v1.Mem_T.PUCHAR == _v2.Mem_T.PUCHAR
   && _v1.Mem_T.PVOID == _v2.Mem_T.PVOID
   && _v1.Mem_T.Pieee80211_scan_entry == _v2.Mem_T.Pieee80211_scan_entry
   && _v1.Mem_T.UCHAR == _v2.Mem_T.UCHAR
   && _v1.Mem_T.VOID == _v2.Mem_T.VOID
   && _v1.Mem_T.ieee80211_scan_entry == _v2.Mem_T.ieee80211_scan_entry
   && _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry
     == _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry
   && _v1.detChoiceCnt == _v2.detChoiceCnt
   && _v1.Res_KERNEL_SOURCE == _v2.Res_KERNEL_SOURCE
   && _v1.Res_PROBED == _v2.Res_PROBED;
  modifies _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR, _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
  ensures MS$_v1.main$_v2.main(old(_v1.OK), 
  old(_v1.Mem), 
  old(_v1.alloc), 
  old(_v1.Mem_T.A1CHAR), 
  old(_v1.Mem_T.A5UCHAR), 
  old(_v1.Mem_T.A6UCHAR), 
  old(_v1.Mem_T.CHAR), 
  old(_v1.Mem_T.INT4), 
  old(_v1.Mem_T.PCHAR), 
  old(_v1.Mem_T.PUCHAR), 
  old(_v1.Mem_T.PVOID), 
  old(_v1.Mem_T.Pieee80211_scan_entry), 
  old(_v1.Mem_T.UCHAR), 
  old(_v1.Mem_T.VOID), 
  old(_v1.Mem_T.ieee80211_scan_entry), 
  old(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v1.detChoiceCnt), 
  old(_v1.Res_KERNEL_SOURCE), 
  old(_v1.Res_PROBED), 
  _v1.alloc, 
  _v1.OK, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, 
  _v1.Mem_T.UCHAR, 
  _v1.result.main$1, 
  old(_v2.OK), 
  old(_v2.Mem), 
  old(_v2.alloc), 
  old(_v2.Mem_T.A1CHAR), 
  old(_v2.Mem_T.A5UCHAR), 
  old(_v2.Mem_T.A6UCHAR), 
  old(_v2.Mem_T.CHAR), 
  old(_v2.Mem_T.INT4), 
  old(_v2.Mem_T.PCHAR), 
  old(_v2.Mem_T.PUCHAR), 
  old(_v2.Mem_T.PVOID), 
  old(_v2.Mem_T.Pieee80211_scan_entry), 
  old(_v2.Mem_T.UCHAR), 
  old(_v2.Mem_T.VOID), 
  old(_v2.Mem_T.ieee80211_scan_entry), 
  old(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry), 
  old(_v2.detChoiceCnt), 
  old(_v2.Res_KERNEL_SOURCE), 
  old(_v2.Res_PROBED), 
  _v2.alloc, 
  _v2.OK, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, 
  _v2.Mem_T.UCHAR, 
  _v2.result.main$1);
  ensures _v1.OK ==> _v2.OK;



implementation MS_Check__v1.main___v2.main() returns (_v1.result.main$1: int, _v2.result.main$1: int)
{
  var inline$_v1.main$0$havoc_stringTemp: int;
  var inline$_v1.main$0$condVal: int;
  var inline$_v1.main$0$ie: int;
  var inline$_v1.main$0$result.giwscan_cb$2: int;
  var inline$_v1.main$0$se: int;
  var inline$_v1.main$0$tempBoogie0: int;
  var inline$_v1.main$0$tempBoogie1: int;
  var inline$_v1.main$0$tempBoogie2: int;
  var inline$_v1.main$0$tempBoogie3: int;
  var inline$_v1.main$0$tempBoogie4: int;
  var inline$_v1.main$0$tempBoogie5: int;
  var inline$_v1.main$0$tempBoogie6: int;
  var inline$_v1.main$0$tempBoogie7: int;
  var inline$_v1.main$0$tempBoogie8: int;
  var inline$_v1.main$0$tempBoogie9: int;
  var inline$_v1.main$0$tempBoogie10: int;
  var inline$_v1.main$0$tempBoogie11: int;
  var inline$_v1.main$0$tempBoogie12: int;
  var inline$_v1.main$0$tempBoogie13: int;
  var inline$_v1.main$0$tempBoogie14: int;
  var inline$_v1.main$0$tempBoogie15: int;
  var inline$_v1.main$0$tempBoogie16: int;
  var inline$_v1.main$0$tempBoogie17: int;
  var inline$_v1.main$0$tempBoogie18: int;
  var inline$_v1.main$0$tempBoogie19: int;
  var inline$_v1.main$0$__havoc_dummy_return: int;
  var inline$_v1.main$0$result.main$1: int;
  var inline$_v1.main$0$_v1.alloc: int;
  var inline$_v1.main$0$_v1.OK: bool;
  var inline$_v1.main$0$_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var inline$_v1.main$0$_v1.Mem_T.UCHAR: [int]int;
  var inline$_v2.main$0$havoc_stringTemp: int;
  var inline$_v2.main$0$condVal: int;
  var inline$_v2.main$0$ie: int;
  var inline$_v2.main$0$result.giwscan_cb$2: int;
  var inline$_v2.main$0$se: int;
  var inline$_v2.main$0$tempBoogie0: int;
  var inline$_v2.main$0$tempBoogie1: int;
  var inline$_v2.main$0$tempBoogie2: int;
  var inline$_v2.main$0$tempBoogie3: int;
  var inline$_v2.main$0$tempBoogie4: int;
  var inline$_v2.main$0$tempBoogie5: int;
  var inline$_v2.main$0$tempBoogie6: int;
  var inline$_v2.main$0$tempBoogie7: int;
  var inline$_v2.main$0$tempBoogie8: int;
  var inline$_v2.main$0$tempBoogie9: int;
  var inline$_v2.main$0$tempBoogie10: int;
  var inline$_v2.main$0$tempBoogie11: int;
  var inline$_v2.main$0$tempBoogie12: int;
  var inline$_v2.main$0$tempBoogie13: int;
  var inline$_v2.main$0$tempBoogie14: int;
  var inline$_v2.main$0$tempBoogie15: int;
  var inline$_v2.main$0$tempBoogie16: int;
  var inline$_v2.main$0$tempBoogie17: int;
  var inline$_v2.main$0$tempBoogie18: int;
  var inline$_v2.main$0$tempBoogie19: int;
  var inline$_v2.main$0$__havoc_dummy_return: int;
  var inline$_v2.main$0$result.main$1: int;
  var inline$_v2.main$0$_v2.alloc: int;
  var inline$_v2.main$0$_v2.OK: bool;
  var inline$_v2.main$0$_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var inline$_v2.main$0$_v2.Mem_T.UCHAR: [int]int;
  var _v1.__HAVOC_det_malloc_1_done: bool;
  var _v1.__HAVOC_det_malloc_in_1_0: int;
  var _v1.__HAVOC_det_malloc_in_1_1: int;
  var _v1.__HAVOC_det_malloc_in_1_2: bool;
  var _v1.__HAVOC_det_malloc_in_1_3: [int]int;
  var _v1.__HAVOC_det_malloc_in_1_4: [int]int;
  var _v1.__HAVOC_det_malloc_out_1_0: int;
  var _v1.__HAVOC_det_malloc_out_1_1: int;
  var _v1.__HAVOC_det_malloc_2_done: bool;
  var _v1.__HAVOC_det_malloc_in_2_0: int;
  var _v1.__HAVOC_det_malloc_in_2_1: int;
  var _v1.__HAVOC_det_malloc_in_2_2: bool;
  var _v1.__HAVOC_det_malloc_in_2_3: [int]int;
  var _v1.__HAVOC_det_malloc_in_2_4: [int]int;
  var _v1.__HAVOC_det_malloc_out_2_0: int;
  var _v1.__HAVOC_det_malloc_out_2_1: int;
  var _v1.giwscan_cb_3_done: bool;
  var _v1.giwscan_cb_in_3_0: int;
  var _v1.giwscan_cb_in_3_1: int;
  var _v1.giwscan_cb_in_3_2: bool;
  var _v1.giwscan_cb_in_3_3: [int]int;
  var _v1.giwscan_cb_in_3_4: [int]int;
  var _v1.giwscan_cb_out_3_0: int;
  var _v1.giwscan_cb_out_3_1: int;
  var _v1.giwscan_cb_out_3_2: bool;
  var _v1.giwscan_cb_out_3_3: [int]int;
  var _v1.__HAVOC_free_4_done: bool;
  var _v1.__HAVOC_free_in_4_0: int;
  var _v1.__HAVOC_free_in_4_1: int;
  var _v1.__HAVOC_free_in_4_2: bool;
  var _v1.__HAVOC_free_in_4_3: [int]int;
  var _v1.__HAVOC_free_in_4_4: [int]int;
  var _v1.__HAVOC_free_5_done: bool;
  var _v1.__HAVOC_free_in_5_0: int;
  var _v1.__HAVOC_free_in_5_1: int;
  var _v1.__HAVOC_free_in_5_2: bool;
  var _v1.__HAVOC_free_in_5_3: [int]int;
  var _v1.__HAVOC_free_in_5_4: [int]int;
  var _v2.__HAVOC_det_malloc_6_done: bool;
  var _v2.__HAVOC_det_malloc_in_6_0: int;
  var _v2.__HAVOC_det_malloc_in_6_1: int;
  var _v2.__HAVOC_det_malloc_in_6_2: bool;
  var _v2.__HAVOC_det_malloc_in_6_3: [int]int;
  var _v2.__HAVOC_det_malloc_in_6_4: [int]int;
  var _v2.__HAVOC_det_malloc_out_6_0: int;
  var _v2.__HAVOC_det_malloc_out_6_1: int;
  var _v2.__HAVOC_det_malloc_7_done: bool;
  var _v2.__HAVOC_det_malloc_in_7_0: int;
  var _v2.__HAVOC_det_malloc_in_7_1: int;
  var _v2.__HAVOC_det_malloc_in_7_2: bool;
  var _v2.__HAVOC_det_malloc_in_7_3: [int]int;
  var _v2.__HAVOC_det_malloc_in_7_4: [int]int;
  var _v2.__HAVOC_det_malloc_out_7_0: int;
  var _v2.__HAVOC_det_malloc_out_7_1: int;
  var _v2.giwscan_cb_8_done: bool;
  var _v2.giwscan_cb_in_8_0: int;
  var _v2.giwscan_cb_in_8_1: int;
  var _v2.giwscan_cb_in_8_2: bool;
  var _v2.giwscan_cb_in_8_3: [int]int;
  var _v2.giwscan_cb_in_8_4: [int]int;
  var _v2.giwscan_cb_out_8_0: int;
  var _v2.giwscan_cb_out_8_1: int;
  var _v2.giwscan_cb_out_8_2: bool;
  var _v2.giwscan_cb_out_8_3: [int]int;
  var _v2.__HAVOC_free_9_done: bool;
  var _v2.__HAVOC_free_in_9_0: int;
  var _v2.__HAVOC_free_in_9_1: int;
  var _v2.__HAVOC_free_in_9_2: bool;
  var _v2.__HAVOC_free_in_9_3: [int]int;
  var _v2.__HAVOC_free_in_9_4: [int]int;
  var _v2.__HAVOC_free_10_done: bool;
  var _v2.__HAVOC_free_in_10_0: int;
  var _v2.__HAVOC_free_in_10_1: int;
  var _v2.__HAVOC_free_in_10_2: bool;
  var _v2.__HAVOC_free_in_10_3: [int]int;
  var _v2.__HAVOC_free_in_10_4: [int]int;
  var store__0__v1.alloc: int;
  var store__0__v1.OK: bool;
  var store__0__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__0__v1.Mem_T.UCHAR: [int]int;
  var store__0__v2.alloc: int;
  var store__0__v2.OK: bool;
  var store__0__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__0__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_1_0_0: int;
  var out__v2.__HAVOC_det_malloc_out_6_0_0: int;
  var store__1__v1.alloc: int;
  var store__1__v1.OK: bool;
  var store__1__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__1__v1.Mem_T.UCHAR: [int]int;
  var store__1__v2.alloc: int;
  var store__1__v2.OK: bool;
  var store__1__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__1__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_1_0_1: int;
  var out__v2.__HAVOC_det_malloc_out_7_0_1: int;
  var store__2__v1.alloc: int;
  var store__2__v1.OK: bool;
  var store__2__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__2__v1.Mem_T.UCHAR: [int]int;
  var store__2__v2.alloc: int;
  var store__2__v2.OK: bool;
  var store__2__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__2__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_2_0_2: int;
  var out__v2.__HAVOC_det_malloc_out_6_0_2: int;
  var store__3__v1.alloc: int;
  var store__3__v1.OK: bool;
  var store__3__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__3__v1.Mem_T.UCHAR: [int]int;
  var store__3__v2.alloc: int;
  var store__3__v2.OK: bool;
  var store__3__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__3__v2.Mem_T.UCHAR: [int]int;
  var out__v1.__HAVOC_det_malloc_out_2_0_3: int;
  var out__v2.__HAVOC_det_malloc_out_7_0_3: int;
  var store__4__v1.alloc: int;
  var store__4__v1.OK: bool;
  var store__4__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__4__v1.Mem_T.UCHAR: [int]int;
  var store__4__v2.alloc: int;
  var store__4__v2.OK: bool;
  var store__4__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__4__v2.Mem_T.UCHAR: [int]int;
  var out__v1.giwscan_cb_out_3_0_4: int;
  var out__v2.giwscan_cb_out_8_0_4: int;
  var store__5__v1.alloc: int;
  var store__5__v1.OK: bool;
  var store__5__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__5__v1.Mem_T.UCHAR: [int]int;
  var store__5__v2.alloc: int;
  var store__5__v2.OK: bool;
  var store__5__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__5__v2.Mem_T.UCHAR: [int]int;
  var store__6__v1.alloc: int;
  var store__6__v1.OK: bool;
  var store__6__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__6__v1.Mem_T.UCHAR: [int]int;
  var store__6__v2.alloc: int;
  var store__6__v2.OK: bool;
  var store__6__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__6__v2.Mem_T.UCHAR: [int]int;
  var store__7__v1.alloc: int;
  var store__7__v1.OK: bool;
  var store__7__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__7__v1.Mem_T.UCHAR: [int]int;
  var store__7__v2.alloc: int;
  var store__7__v2.OK: bool;
  var store__7__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__7__v2.Mem_T.UCHAR: [int]int;
  var store__8__v1.alloc: int;
  var store__8__v1.OK: bool;
  var store__8__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__8__v1.Mem_T.UCHAR: [int]int;
  var store__8__v2.alloc: int;
  var store__8__v2.OK: bool;
  var store__8__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry: [int]int;
  var store__8__v2.Mem_T.UCHAR: [int]int;

  START:
    _v1.__HAVOC_det_malloc_1_done, _v1.__HAVOC_det_malloc_2_done, _v1.giwscan_cb_3_done, _v1.__HAVOC_free_4_done, _v1.__HAVOC_free_5_done, _v2.__HAVOC_det_malloc_6_done, _v2.__HAVOC_det_malloc_7_done, _v2.giwscan_cb_8_done, _v2.__HAVOC_free_9_done, _v2.__HAVOC_free_10_done := false, false, false, false, false, false, false, false, false, false;
    goto inline$_v1.main$0$Entry;

  inline$_v1.main$0$Entry:
    havoc inline$_v1.main$0$havoc_stringTemp, inline$_v1.main$0$condVal, inline$_v1.main$0$ie, inline$_v1.main$0$result.giwscan_cb$2, inline$_v1.main$0$se, inline$_v1.main$0$tempBoogie0, inline$_v1.main$0$tempBoogie1, inline$_v1.main$0$tempBoogie2, inline$_v1.main$0$tempBoogie3, inline$_v1.main$0$tempBoogie4, inline$_v1.main$0$tempBoogie5, inline$_v1.main$0$tempBoogie6, inline$_v1.main$0$tempBoogie7, inline$_v1.main$0$tempBoogie8, inline$_v1.main$0$tempBoogie9, inline$_v1.main$0$tempBoogie10, inline$_v1.main$0$tempBoogie11, inline$_v1.main$0$tempBoogie12, inline$_v1.main$0$tempBoogie13, inline$_v1.main$0$tempBoogie14, inline$_v1.main$0$tempBoogie15, inline$_v1.main$0$tempBoogie16, inline$_v1.main$0$tempBoogie17, inline$_v1.main$0$tempBoogie18, inline$_v1.main$0$tempBoogie19, inline$_v1.main$0$__havoc_dummy_return, inline$_v1.main$0$result.main$1;
    inline$_v1.main$0$_v1.alloc := _v1.alloc;
    inline$_v1.main$0$_v1.OK := _v1.OK;
    inline$_v1.main$0$_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry := _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry;
    inline$_v1.main$0$_v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR;
    goto inline$_v1.main$0$anon0#2;

  inline$_v1.main$0$anon0#2:
    inline$_v1.main$0$havoc_stringTemp := 0;
    goto inline$_v1.main$0$start#2;

  inline$_v1.main$0$start#2:
    _v1.__HAVOC_det_malloc_in_1_0, _v1.__HAVOC_det_malloc_in_1_1, _v1.__HAVOC_det_malloc_in_1_2, _v1.__HAVOC_det_malloc_in_1_3, _v1.__HAVOC_det_malloc_in_1_4 := 5, _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    call inline$_v1.main$0$ie := _v1.__HAVOC_det_malloc(5);
    _v1.__HAVOC_det_malloc_1_done := true;
    _v1.__HAVOC_det_malloc_out_1_0, _v1.__HAVOC_det_malloc_out_1_1 := inline$_v1.main$0$ie, _v1.alloc;
    inline$_v1.main$0$result.giwscan_cb$2 := 0;
    inline$_v1.main$0$result.main$1 := 0;
    _v1.__HAVOC_det_malloc_in_2_0, _v1.__HAVOC_det_malloc_in_2_1, _v1.__HAVOC_det_malloc_in_2_2, _v1.__HAVOC_det_malloc_in_2_3, _v1.__HAVOC_det_malloc_in_2_4 := 4, _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    call inline$_v1.main$0$se := _v1.__HAVOC_det_malloc(4);
    _v1.__HAVOC_det_malloc_2_done := true;
    _v1.__HAVOC_det_malloc_out_2_0, _v1.__HAVOC_det_malloc_out_2_1 := inline$_v1.main$0$se, _v1.alloc;
    goto inline$_v1.main$0$label_3#2;

  inline$_v1.main$0$label_3#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 62} true;
    goto inline$_v1.main$0$label_4#2;

  inline$_v1.main$0$label_4#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 63} true;
    goto inline$_v1.main$0$label_5#2;

  inline$_v1.main$0$label_5#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 64} true;
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se))
     == 1;
    assert true;
    _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry := _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se) := inline$_v1.main$0$ie];
    assume _v2.value_is(_v1.__ctobpl_const_47, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)]);
    goto inline$_v1.main$0$label_6#2;

  inline$_v1.main$0$label_6#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 65} true;
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
        1, 
        0))
     == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
  1, 
  0) := 200];
    assume _v2.value_is(_v1.__ctobpl_const_48, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_49, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
    1, 
    0)]);
    goto inline$_v1.main$0$label_7#2;

  inline$_v1.main$0$label_7#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 66} true;
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
  0);
    _v1.OK := _v1.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
        1, 
        1))
     == 1;
    assert true;
    _v1.Mem_T.UCHAR := _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
  1, 
  1) := 3];
    assume _v2.value_is(_v1.__ctobpl_const_50, 
  _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)]);
    assume _v2.value_is(_v1.__ctobpl_const_51, 
  _v1.Mem_T.UCHAR[_v2.INT_PLUS(_v1.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v1.main$0$se)], 
    1, 
    1)]);
    goto inline$_v1.main$0$label_8#2;

  inline$_v1.main$0$label_8#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 68} true;
    assume _v2.INT_GT(inline$_v1.main$0$se, 0);
    assume _v2.INT_GT(inline$_v1.main$0$se, 0);
    _v1.giwscan_cb_in_3_0, _v1.giwscan_cb_in_3_1, _v1.giwscan_cb_in_3_2, _v1.giwscan_cb_in_3_3, _v1.giwscan_cb_in_3_4 := inline$_v1.main$0$se, _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    call inline$_v1.main$0$result.giwscan_cb$2 := _v1.giwscan_cb(inline$_v1.main$0$se);
    _v1.giwscan_cb_3_done := true;
    _v1.giwscan_cb_out_3_0, _v1.giwscan_cb_out_3_1, _v1.giwscan_cb_out_3_2, _v1.giwscan_cb_out_3_3 := inline$_v1.main$0$result.giwscan_cb$2, _v1.alloc, _v1.OK, _v1.Mem_T.UCHAR;
    goto inline$_v1.main$0$label_11#2;

  inline$_v1.main$0$label_11#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 70} true;
    inline$_v1.main$0$result.main$1 := 0;
    goto inline$_v1.main$0$label_1#2;

  inline$_v1.main$0$label_1#2:
    _v1.OK := _v1.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\bad\interproc_bad.c"} {:sourceline 71} true;
    _v1.__HAVOC_free_in_4_0, _v1.__HAVOC_free_in_4_1, _v1.__HAVOC_free_in_4_2, _v1.__HAVOC_free_in_4_3, _v1.__HAVOC_free_in_4_4 := inline$_v1.main$0$ie, _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    call _v1.__HAVOC_free(inline$_v1.main$0$ie);
    _v1.__HAVOC_free_4_done := true;
    _v1.__HAVOC_free_in_5_0, _v1.__HAVOC_free_in_5_1, _v1.__HAVOC_free_in_5_2, _v1.__HAVOC_free_in_5_3, _v1.__HAVOC_free_in_5_4 := inline$_v1.main$0$se, _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    call _v1.__HAVOC_free(inline$_v1.main$0$se);
    _v1.__HAVOC_free_5_done := true;
    goto inline$_v1.main$0$Return;

  inline$_v1.main$0$Return:
    assume true;
    _v1.result.main$1 := inline$_v1.main$0$result.main$1;
    goto START$1;

  START$1:
    goto inline$_v2.main$0$Entry;

  inline$_v2.main$0$Entry:
    havoc inline$_v2.main$0$havoc_stringTemp, inline$_v2.main$0$condVal, inline$_v2.main$0$ie, inline$_v2.main$0$result.giwscan_cb$2, inline$_v2.main$0$se, inline$_v2.main$0$tempBoogie0, inline$_v2.main$0$tempBoogie1, inline$_v2.main$0$tempBoogie2, inline$_v2.main$0$tempBoogie3, inline$_v2.main$0$tempBoogie4, inline$_v2.main$0$tempBoogie5, inline$_v2.main$0$tempBoogie6, inline$_v2.main$0$tempBoogie7, inline$_v2.main$0$tempBoogie8, inline$_v2.main$0$tempBoogie9, inline$_v2.main$0$tempBoogie10, inline$_v2.main$0$tempBoogie11, inline$_v2.main$0$tempBoogie12, inline$_v2.main$0$tempBoogie13, inline$_v2.main$0$tempBoogie14, inline$_v2.main$0$tempBoogie15, inline$_v2.main$0$tempBoogie16, inline$_v2.main$0$tempBoogie17, inline$_v2.main$0$tempBoogie18, inline$_v2.main$0$tempBoogie19, inline$_v2.main$0$__havoc_dummy_return, inline$_v2.main$0$result.main$1;
    inline$_v2.main$0$_v2.alloc := _v2.alloc;
    inline$_v2.main$0$_v2.OK := _v2.OK;
    inline$_v2.main$0$_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry := _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry;
    inline$_v2.main$0$_v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR;
    goto inline$_v2.main$0$anon0#2;

  inline$_v2.main$0$anon0#2:
    inline$_v2.main$0$havoc_stringTemp := 0;
    goto inline$_v2.main$0$start#2;

  inline$_v2.main$0$start#2:
    _v2.__HAVOC_det_malloc_in_6_0, _v2.__HAVOC_det_malloc_in_6_1, _v2.__HAVOC_det_malloc_in_6_2, _v2.__HAVOC_det_malloc_in_6_3, _v2.__HAVOC_det_malloc_in_6_4 := 5, _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    call inline$_v2.main$0$ie := _v2.__HAVOC_det_malloc(5);
    _v2.__HAVOC_det_malloc_6_done := true;
    _v2.__HAVOC_det_malloc_out_6_0, _v2.__HAVOC_det_malloc_out_6_1 := inline$_v2.main$0$ie, _v2.alloc;
    inline$_v2.main$0$result.giwscan_cb$2 := 0;
    inline$_v2.main$0$result.main$1 := 0;
    _v2.__HAVOC_det_malloc_in_7_0, _v2.__HAVOC_det_malloc_in_7_1, _v2.__HAVOC_det_malloc_in_7_2, _v2.__HAVOC_det_malloc_in_7_3, _v2.__HAVOC_det_malloc_in_7_4 := 4, _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    call inline$_v2.main$0$se := _v2.__HAVOC_det_malloc(4);
    _v2.__HAVOC_det_malloc_7_done := true;
    _v2.__HAVOC_det_malloc_out_7_0, _v2.__HAVOC_det_malloc_out_7_1 := inline$_v2.main$0$se, _v2.alloc;
    goto inline$_v2.main$0$label_3#2;

  inline$_v2.main$0$label_3#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 63} true;
    goto inline$_v2.main$0$label_4#2;

  inline$_v2.main$0$label_4#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 64} true;
    goto inline$_v2.main$0$label_5#2;

  inline$_v2.main$0$label_5#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 65} true;
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se))
     == 1;
    assert true;
    _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry := _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se) := inline$_v2.main$0$ie];
    assume _v2.value_is(_v2.__ctobpl_const_48, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)]);
    goto inline$_v2.main$0$label_6#2;

  inline$_v2.main$0$label_6#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 66} true;
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
        1, 
        0))
     == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
  1, 
  0) := 200];
    assume _v2.value_is(_v2.__ctobpl_const_49, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_50, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
    1, 
    0)]);
    goto inline$_v2.main$0$label_7#2;

  inline$_v2.main$0$label_7#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 67} true;
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se))
     == 1;
    assert true;
    assume _v2.INT_GEQ(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
  0);
    _v2.OK := _v2.OK
   && _v2.Res_VALID_REGION(_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
        1, 
        1))
     == 1;
    assert true;
    _v2.Mem_T.UCHAR := _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
  1, 
  1) := 3];
    assume _v2.value_is(_v2.__ctobpl_const_51, 
  _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)]);
    assume _v2.value_is(_v2.__ctobpl_const_52, 
  _v2.Mem_T.UCHAR[_v2.INT_PLUS(_v2.Mem_T.se_rsn_ie_ieee80211_scan_entry[_v2.se_rsn_ie_ieee80211_scan_entry(inline$_v2.main$0$se)], 
    1, 
    1)]);
    goto inline$_v2.main$0$label_8#2;

  inline$_v2.main$0$label_8#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 69} true;
    assume _v2.INT_GT(inline$_v2.main$0$se, 0);
    assume _v2.INT_GT(inline$_v2.main$0$se, 0);
    _v2.giwscan_cb_in_8_0, _v2.giwscan_cb_in_8_1, _v2.giwscan_cb_in_8_2, _v2.giwscan_cb_in_8_3, _v2.giwscan_cb_in_8_4 := inline$_v2.main$0$se, _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    call inline$_v2.main$0$result.giwscan_cb$2 := _v2.giwscan_cb(inline$_v2.main$0$se);
    _v2.giwscan_cb_8_done := true;
    _v2.giwscan_cb_out_8_0, _v2.giwscan_cb_out_8_1, _v2.giwscan_cb_out_8_2, _v2.giwscan_cb_out_8_3 := inline$_v2.main$0$result.giwscan_cb$2, _v2.alloc, _v2.OK, _v2.Mem_T.UCHAR;
    goto inline$_v2.main$0$label_11#2;

  inline$_v2.main$0$label_11#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 71} true;
    inline$_v2.main$0$result.main$1 := 0;
    goto inline$_v2.main$0$label_1#2;

  inline$_v2.main$0$label_1#2:
    _v2.OK := _v2.OK && true;
    assert {:sourcefile "d:\tvm\projects\symb_diff\benchmarks\verisec-suite\programs\apps\madwifi\cve-2006-6332\ok\interproc_ok.c"} {:sourceline 72} true;
    _v2.__HAVOC_free_in_9_0, _v2.__HAVOC_free_in_9_1, _v2.__HAVOC_free_in_9_2, _v2.__HAVOC_free_in_9_3, _v2.__HAVOC_free_in_9_4 := inline$_v2.main$0$ie, _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    call _v2.__HAVOC_free(inline$_v2.main$0$ie);
    _v2.__HAVOC_free_9_done := true;
    _v2.__HAVOC_free_in_10_0, _v2.__HAVOC_free_in_10_1, _v2.__HAVOC_free_in_10_2, _v2.__HAVOC_free_in_10_3, _v2.__HAVOC_free_in_10_4 := inline$_v2.main$0$se, _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    call _v2.__HAVOC_free(inline$_v2.main$0$se);
    _v2.__HAVOC_free_10_done := true;
    goto inline$_v2.main$0$Return;

  inline$_v2.main$0$Return:
    assume true;
    _v2.result.main$1 := inline$_v2.main$0$result.main$1;
    goto START$2;

  START$2:
    goto MS_L_0_8;

  MS_L_0_0:
    goto MS_L_taken_0, MS_L_not_taken_0;

  MS_L_taken_0:
    assume _v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_6_done;
    store__0__v1.alloc, store__0__v1.OK, store__0__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__0__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__0__v2.alloc, store__0__v2.OK, store__0__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__0__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_1_1, _v1.__HAVOC_det_malloc_in_1_2, _v1.__HAVOC_det_malloc_in_1_3, _v1.__HAVOC_det_malloc_in_1_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_6_1, _v2.__HAVOC_det_malloc_in_6_2, _v2.__HAVOC_det_malloc_in_6_3, _v2.__HAVOC_det_malloc_in_6_4;
    call out__v1.__HAVOC_det_malloc_out_1_0_0, out__v2.__HAVOC_det_malloc_out_6_0_0 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_1_0, _v2.__HAVOC_det_malloc_in_6_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_1_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_6_1;
    assume _v1.__HAVOC_det_malloc_out_1_0 == out__v1.__HAVOC_det_malloc_out_1_0_0
   && _v2.__HAVOC_det_malloc_out_6_0 == out__v2.__HAVOC_det_malloc_out_6_0_0;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__0__v1.alloc, store__0__v1.OK, store__0__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__0__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__0__v2.alloc, store__0__v2.OK, store__0__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__0__v2.Mem_T.UCHAR;
    goto MS_L_meet_0;

  MS_L_not_taken_0:
    assume !(_v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_6_done);
    goto MS_L_meet_0;

  MS_L_meet_0:
    return;

  MS_L_0_1:
    goto MS_L_taken_1, MS_L_not_taken_1;

  MS_L_taken_1:
    assume _v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_7_done;
    store__1__v1.alloc, store__1__v1.OK, store__1__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__1__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__1__v2.alloc, store__1__v2.OK, store__1__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__1__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_1_1, _v1.__HAVOC_det_malloc_in_1_2, _v1.__HAVOC_det_malloc_in_1_3, _v1.__HAVOC_det_malloc_in_1_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_7_1, _v2.__HAVOC_det_malloc_in_7_2, _v2.__HAVOC_det_malloc_in_7_3, _v2.__HAVOC_det_malloc_in_7_4;
    call out__v1.__HAVOC_det_malloc_out_1_0_1, out__v2.__HAVOC_det_malloc_out_7_0_1 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_1_0, _v2.__HAVOC_det_malloc_in_7_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_1_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_7_1;
    assume _v1.__HAVOC_det_malloc_out_1_0 == out__v1.__HAVOC_det_malloc_out_1_0_1
   && _v2.__HAVOC_det_malloc_out_7_0 == out__v2.__HAVOC_det_malloc_out_7_0_1;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__1__v1.alloc, store__1__v1.OK, store__1__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__1__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__1__v2.alloc, store__1__v2.OK, store__1__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__1__v2.Mem_T.UCHAR;
    goto MS_L_meet_1;

  MS_L_not_taken_1:
    assume !(_v1.__HAVOC_det_malloc_1_done && _v2.__HAVOC_det_malloc_7_done);
    goto MS_L_meet_1;

  MS_L_meet_1:
    goto MS_L_0_0;

  MS_L_0_2:
    goto MS_L_taken_2, MS_L_not_taken_2;

  MS_L_taken_2:
    assume _v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_6_done;
    store__2__v1.alloc, store__2__v1.OK, store__2__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__2__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__2__v2.alloc, store__2__v2.OK, store__2__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__2__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_2_1, _v1.__HAVOC_det_malloc_in_2_2, _v1.__HAVOC_det_malloc_in_2_3, _v1.__HAVOC_det_malloc_in_2_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_6_1, _v2.__HAVOC_det_malloc_in_6_2, _v2.__HAVOC_det_malloc_in_6_3, _v2.__HAVOC_det_malloc_in_6_4;
    call out__v1.__HAVOC_det_malloc_out_2_0_2, out__v2.__HAVOC_det_malloc_out_6_0_2 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_2_0, _v2.__HAVOC_det_malloc_in_6_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_2_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_6_1;
    assume _v1.__HAVOC_det_malloc_out_2_0 == out__v1.__HAVOC_det_malloc_out_2_0_2
   && _v2.__HAVOC_det_malloc_out_6_0 == out__v2.__HAVOC_det_malloc_out_6_0_2;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__2__v1.alloc, store__2__v1.OK, store__2__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__2__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__2__v2.alloc, store__2__v2.OK, store__2__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__2__v2.Mem_T.UCHAR;
    goto MS_L_meet_2;

  MS_L_not_taken_2:
    assume !(_v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_6_done);
    goto MS_L_meet_2;

  MS_L_meet_2:
    goto MS_L_0_1;

  MS_L_0_3:
    goto MS_L_taken_3, MS_L_not_taken_3;

  MS_L_taken_3:
    assume _v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_7_done;
    store__3__v1.alloc, store__3__v1.OK, store__3__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__3__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__3__v2.alloc, store__3__v2.OK, store__3__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__3__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_det_malloc_in_2_1, _v1.__HAVOC_det_malloc_in_2_2, _v1.__HAVOC_det_malloc_in_2_3, _v1.__HAVOC_det_malloc_in_2_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_det_malloc_in_7_1, _v2.__HAVOC_det_malloc_in_7_2, _v2.__HAVOC_det_malloc_in_7_3, _v2.__HAVOC_det_malloc_in_7_4;
    call out__v1.__HAVOC_det_malloc_out_2_0_3, out__v2.__HAVOC_det_malloc_out_7_0_3 := MS_Check__v1.__HAVOC_det_malloc___v2.__HAVOC_det_malloc(_v1.__HAVOC_det_malloc_in_2_0, _v2.__HAVOC_det_malloc_in_7_0);
    assume _v1.alloc == _v1.__HAVOC_det_malloc_out_2_1;
    assume _v2.alloc == _v2.__HAVOC_det_malloc_out_7_1;
    assume _v1.__HAVOC_det_malloc_out_2_0 == out__v1.__HAVOC_det_malloc_out_2_0_3
   && _v2.__HAVOC_det_malloc_out_7_0 == out__v2.__HAVOC_det_malloc_out_7_0_3;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__3__v1.alloc, store__3__v1.OK, store__3__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__3__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__3__v2.alloc, store__3__v2.OK, store__3__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__3__v2.Mem_T.UCHAR;
    goto MS_L_meet_3;

  MS_L_not_taken_3:
    assume !(_v1.__HAVOC_det_malloc_2_done && _v2.__HAVOC_det_malloc_7_done);
    goto MS_L_meet_3;

  MS_L_meet_3:
    goto MS_L_0_2;

  MS_L_0_4:
    goto MS_L_taken_4, MS_L_not_taken_4;

  MS_L_taken_4:
    assume _v1.giwscan_cb_3_done && _v2.giwscan_cb_8_done;
    store__4__v1.alloc, store__4__v1.OK, store__4__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__4__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__4__v2.alloc, store__4__v2.OK, store__4__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__4__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.giwscan_cb_in_3_1, _v1.giwscan_cb_in_3_2, _v1.giwscan_cb_in_3_3, _v1.giwscan_cb_in_3_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.giwscan_cb_in_8_1, _v2.giwscan_cb_in_8_2, _v2.giwscan_cb_in_8_3, _v2.giwscan_cb_in_8_4;
    call out__v1.giwscan_cb_out_3_0_4, out__v2.giwscan_cb_out_8_0_4 := MS_Check__v1.giwscan_cb___v2.giwscan_cb(_v1.giwscan_cb_in_3_0, _v2.giwscan_cb_in_8_0);
    assume _v1.alloc == _v1.giwscan_cb_out_3_1
   && (_v1.OK <==> _v1.giwscan_cb_out_3_2)
   && _v1.Mem_T.UCHAR == _v1.giwscan_cb_out_3_3;
    assume _v2.alloc == _v2.giwscan_cb_out_8_1
   && (_v2.OK <==> _v2.giwscan_cb_out_8_2)
   && _v2.Mem_T.UCHAR == _v2.giwscan_cb_out_8_3;
    assume _v1.giwscan_cb_out_3_0 == out__v1.giwscan_cb_out_3_0_4
   && _v2.giwscan_cb_out_8_0 == out__v2.giwscan_cb_out_8_0_4;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__4__v1.alloc, store__4__v1.OK, store__4__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__4__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__4__v2.alloc, store__4__v2.OK, store__4__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__4__v2.Mem_T.UCHAR;
    goto MS_L_meet_4;

  MS_L_not_taken_4:
    assume !(_v1.giwscan_cb_3_done && _v2.giwscan_cb_8_done);
    goto MS_L_meet_4;

  MS_L_meet_4:
    goto MS_L_0_3;

  MS_L_0_5:
    goto MS_L_taken_5, MS_L_not_taken_5;

  MS_L_taken_5:
    assume _v1.__HAVOC_free_4_done && _v2.__HAVOC_free_9_done;
    store__5__v1.alloc, store__5__v1.OK, store__5__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__5__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__5__v2.alloc, store__5__v2.OK, store__5__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__5__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_4_1, _v1.__HAVOC_free_in_4_2, _v1.__HAVOC_free_in_4_3, _v1.__HAVOC_free_in_4_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_9_1, _v2.__HAVOC_free_in_9_2, _v2.__HAVOC_free_in_9_3, _v2.__HAVOC_free_in_9_4;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_4_0, _v2.__HAVOC_free_in_9_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__5__v1.alloc, store__5__v1.OK, store__5__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__5__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__5__v2.alloc, store__5__v2.OK, store__5__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__5__v2.Mem_T.UCHAR;
    goto MS_L_meet_5;

  MS_L_not_taken_5:
    assume !(_v1.__HAVOC_free_4_done && _v2.__HAVOC_free_9_done);
    goto MS_L_meet_5;

  MS_L_meet_5:
    goto MS_L_0_4;

  MS_L_0_6:
    goto MS_L_taken_6, MS_L_not_taken_6;

  MS_L_taken_6:
    assume _v1.__HAVOC_free_4_done && _v2.__HAVOC_free_10_done;
    store__6__v1.alloc, store__6__v1.OK, store__6__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__6__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__6__v2.alloc, store__6__v2.OK, store__6__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__6__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_4_1, _v1.__HAVOC_free_in_4_2, _v1.__HAVOC_free_in_4_3, _v1.__HAVOC_free_in_4_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_10_1, _v2.__HAVOC_free_in_10_2, _v2.__HAVOC_free_in_10_3, _v2.__HAVOC_free_in_10_4;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_4_0, _v2.__HAVOC_free_in_10_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__6__v1.alloc, store__6__v1.OK, store__6__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__6__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__6__v2.alloc, store__6__v2.OK, store__6__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__6__v2.Mem_T.UCHAR;
    goto MS_L_meet_6;

  MS_L_not_taken_6:
    assume !(_v1.__HAVOC_free_4_done && _v2.__HAVOC_free_10_done);
    goto MS_L_meet_6;

  MS_L_meet_6:
    goto MS_L_0_5;

  MS_L_0_7:
    goto MS_L_taken_7, MS_L_not_taken_7;

  MS_L_taken_7:
    assume _v1.__HAVOC_free_5_done && _v2.__HAVOC_free_9_done;
    store__7__v1.alloc, store__7__v1.OK, store__7__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__7__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__7__v2.alloc, store__7__v2.OK, store__7__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__7__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_5_1, _v1.__HAVOC_free_in_5_2, _v1.__HAVOC_free_in_5_3, _v1.__HAVOC_free_in_5_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_9_1, _v2.__HAVOC_free_in_9_2, _v2.__HAVOC_free_in_9_3, _v2.__HAVOC_free_in_9_4;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_5_0, _v2.__HAVOC_free_in_9_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__7__v1.alloc, store__7__v1.OK, store__7__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__7__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__7__v2.alloc, store__7__v2.OK, store__7__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__7__v2.Mem_T.UCHAR;
    goto MS_L_meet_7;

  MS_L_not_taken_7:
    assume !(_v1.__HAVOC_free_5_done && _v2.__HAVOC_free_9_done);
    goto MS_L_meet_7;

  MS_L_meet_7:
    goto MS_L_0_6;

  MS_L_0_8:
    goto MS_L_taken_8, MS_L_not_taken_8;

  MS_L_taken_8:
    assume _v1.__HAVOC_free_5_done && _v2.__HAVOC_free_10_done;
    store__8__v1.alloc, store__8__v1.OK, store__8__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__8__v1.Mem_T.UCHAR := _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR;
    store__8__v2.alloc, store__8__v2.OK, store__8__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__8__v2.Mem_T.UCHAR := _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := _v1.__HAVOC_free_in_5_1, _v1.__HAVOC_free_in_5_2, _v1.__HAVOC_free_in_5_3, _v1.__HAVOC_free_in_5_4;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := _v2.__HAVOC_free_in_10_1, _v2.__HAVOC_free_in_10_2, _v2.__HAVOC_free_in_10_3, _v2.__HAVOC_free_in_10_4;
    call MS_Check__v1.__HAVOC_free___v2.__HAVOC_free(_v1.__HAVOC_free_in_5_0, _v2.__HAVOC_free_in_10_0);
    assume true;
    assume true;
    assume true;
    _v1.alloc, _v1.OK, _v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v1.Mem_T.UCHAR := store__8__v1.alloc, store__8__v1.OK, store__8__v1.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__8__v1.Mem_T.UCHAR;
    _v2.alloc, _v2.OK, _v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, _v2.Mem_T.UCHAR := store__8__v2.alloc, store__8__v2.OK, store__8__v2.Mem_T.se_rsn_ie_ieee80211_scan_entry, store__8__v2.Mem_T.UCHAR;
    goto MS_L_meet_8;

  MS_L_not_taken_8:
    assume !(_v1.__HAVOC_free_5_done && _v2.__HAVOC_free_10_done);
    goto MS_L_meet_8;

  MS_L_meet_8:
    goto MS_L_0_7;
}


