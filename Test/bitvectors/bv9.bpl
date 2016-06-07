// RUN: %boogie -proverOpt:OPTIMIZE_FOR_BV=true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure foo();

implementation foo()
{
    assert (forall Q#a$1^15.32#tc1: bv64, Q#b$1^15.32#tc1: bv64, Q#c$1^15.32#tc1: bv64 :: true && true && true ==> ($bv_bvadd64(Q#a$1^15.32#tc1, Q#b$1^15.32#tc1) == Q#c$1^15.32#tc1 || $bv_bvadd64($bv_bvadd64(Q#a$1^15.32#tc1, Q#b$1^15.32#tc1), 1bv64) == Q#c$1^15.32#tc1) && (if Q#c$1^15.32#tc1 == $bv_bvadd64(Q#a$1^15.32#tc1, Q#b$1^15.32#tc1) then $bv_bvugt64(Q#a$1^15.32#tc1, $bv_bvsub64(18446744073709551615bv64, Q#b$1^15.32#tc1)) else $bv_bvuge64(Q#a$1^15.32#tc1, $bv_bvsub64(18446744073709551615bv64, Q#b$1^15.32#tc1))) ==> $bv_bvlshr64($bv_bvxor64($bv_bvor64(Q#a$1^15.32#tc1, Q#b$1^15.32#tc1), $bv_bvand64($bv_bvxor64(Q#a$1^15.32#tc1, Q#b$1^15.32#tc1), Q#c$1^15.32#tc1)), 0bv32 ++ 63bv32) == 1bv64);
}

function {:bvbuiltin "bvlshr"} $bv_bvlshr64(p1: bv64, p2: bv64) : bv64;

function {:bvbuiltin "bvand"} $bv_bvand64(p1: bv64, p2: bv64) : bv64;

function {:bvbuiltin "bvor"} $bv_bvor64(p1: bv64, p2: bv64) : bv64;

function {:bvbuiltin "bvxor"} $bv_bvxor64(p1: bv64, p2: bv64) : bv64;

function {:bvbuiltin "bvuge"} $bv_bvuge64(p1: bv64, p2: bv64) : bool;

function {:bvbuiltin "bvugt"} $bv_bvugt64(p1: bv64, p2: bv64) : bool;

function {:bvbuiltin "bvsub"} $bv_bvsub64(p1: bv64, p2: bv64) : bv64;

function {:bvbuiltin "bvadd"} $bv_bvadd64(p1: bv64, p2: bv64) : bv64;

