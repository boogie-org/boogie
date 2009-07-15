// -----------------------------------------------------------------------
// Verified C prelude
// version 42
// -----------------------------------------------------------------------

// ldc is left off, use 17bv32 and the like
// bv to/from int functions are not provided by z3
// Use ==/!= instead of ceq/cne.i4/i8 (could be axiomatized, but that would just slow things down)

// Functions starting with $_ are internal to the prelude. The rest is the interface.

// -----------------------------------------------------------------------
// Types
// -----------------------------------------------------------------------

type $ptr;
type $mem;

// -----------------------------------------------------------------------
// Pointers and memory model
// -----------------------------------------------------------------------

const $ldnull:$ptr;

function $ld.i1(m:$mem, p:$ptr) returns(bv32);
function $ld.i2(m:$mem, p:$ptr) returns(bv32);
function $ld.i4(m:$mem, p:$ptr) returns(bv32);
function $ld.i8(m:$mem, p:$ptr) returns(bv64);
function $ld.u1(m:$mem, p:$ptr) returns(bv32);
function $ld.u2(m:$mem, p:$ptr) returns(bv32);
function $ld.ptr(m:$mem, p:$ptr) returns($ptr);

function $st.i1(m:$mem, p:$ptr, v:bv32) returns($mem);
function $st.i2(m:$mem, p:$ptr, v:bv32) returns($mem);
function $st.i4(m:$mem, p:$ptr, v:bv32) returns($mem);
function $st.i8(m:$mem, p:$ptr, v:bv64) returns($mem);
function $st.ptr(m:$mem, p:$ptr, v:$ptr) returns($mem);

function $add.ptr(p:$ptr, off:bv64, elsize:bv64) returns($ptr);
function $sub.ptr(p1:$ptr, p2:$ptr) returns(bv64);

function $_ptr(r:ref, off:bv64) returns($ptr);
function $offset(p:$ptr) returns(bv64);
function $base(p:$ptr) returns(ref);
function $_end(p:$ptr, len:bv64) returns(bv64);

axiom $ldnull == $_ptr(null, 0bv64);

axiom (forall p:$ptr, q:$ptr :: { $sub.ptr(p, q) }
  $base(p) == $base(q) ==> $sub.ptr(p, q) == $sub.i8($offset(p), $offset(q)));

axiom (forall p:$ptr, o:bv64, sz:bv64 :: { $add.ptr(p, o, sz) }
    $add.ptr(p, o, sz) == $_ptr($base(p), $add.i8($offset(p), $mul.i8(o, sz))));

axiom (forall i:bv64, r:ref :: $offset($_ptr(r, i)) == i);
axiom (forall i:bv64, r:ref :: $base($_ptr(r, i)) == r);
axiom (forall p:$ptr, len:bv64 :: { $_end(p, len) } $_end(p, len) == $add.i8($offset(p), len));

// expensive, do we need it?
//axiom (forall p1: $ptr, p2: $ptr:: { $offset(p1), $offset(p2) }
//        ($base(p1) == $base(p2) && $offset(p1) == $offset(p2)) ==> p1 == p2);

// -----------------------------------------------------------------------
// Native Z3 BV memory model
// -----------------------------------------------------------------------

function {:bvbuiltin "sign_extend 24"} $_sign_extend.8.32(v:bv8) returns(bv32);
function {:bvbuiltin "sign_extend 16"} $_sign_extend.16.32(v:bv16) returns(bv32);
function {:bvbuiltin "sign_extend 32"} $_sign_extend.32.64(v:bv32) returns(bv64);

function $_get_byte(m:$mem, r:ref, off:bv64) returns(bv8);
function $_set_byte(m:$mem, r:ref, off:bv64, v:bv8) returns($mem);

axiom {:ignore "bvInt"} (forall m:$mem, r:ref, off:bv64, v:bv8 :: 
  $_get_byte($_set_byte(m, r, off, v), r, off) == v); 

axiom {:ignore "bvInt"} (forall m:$mem, r1:ref, r2:ref, off1:bv64, off2:bv64, v:bv8 :: 
  r1 != r2 ==>
    $_get_byte($_set_byte(m, r1, off1, v), r2, off2) == $_get_byte(m, r2, off2));

axiom {:ignore "bvInt"} (forall m:$mem, r1:ref, r2:ref, off1:bv64, off2:bv64, v:bv8 :: 
  off1 != off2 ==>
    $_get_byte($_set_byte(m, r1, off1, v), r2, off2) == $_get_byte(m, r2, off2));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr ::  { $ld.i4(m, p) }
    $ld.i4(m, p) ==
      $_get_byte(m, $base(p), $add.i8($offset(p), 3bv64)) ++ $_get_byte(m, $base(p), $add.i8($offset(p), 2bv64)) ++ 
      $_get_byte(m, $base(p), $add.i8($offset(p), 1bv64)) ++ $_get_byte(m, $base(p), $offset(p)));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr :: { $ld.i8(m, p) }
    $ld.i8(m, p) ==
      $_get_byte(m, $base(p), $add.i8($offset(p), 7bv64)) ++ $_get_byte(m, $base(p), $add.i8($offset(p), 6bv64)) ++ 
      $_get_byte(m, $base(p), $add.i8($offset(p), 5bv64)) ++ $_get_byte(m, $base(p), $add.i8($offset(p), 4bv64)) ++
      $_get_byte(m, $base(p), $add.i8($offset(p), 3bv64)) ++ $_get_byte(m, $base(p), $add.i8($offset(p), 2bv64)) ++ 
      $_get_byte(m, $base(p), $add.i8($offset(p), 1bv64)) ++ $_get_byte(m, $base(p), $offset(p)));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr :: { $ld.u2(m, p) }
    $ld.u2(m, p) == 0bv16 ++ $_get_byte(m, $base(p), $add.i8($offset(p), 1bv64)) ++ $_get_byte(m, $base(p), $offset(p)));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr :: { $ld.u1(m, p) }
    $ld.u1(m, p) == 0bv24 ++ $_get_byte(m, $base(p), $offset(p)));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr :: { $ld.i2(m, p) }
    $ld.i2(m, p) == $conv.i4.to.i2($ld.u2(m, p)));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr :: { $ld.i1(m, p) } 
    $ld.i1(m, p) == $conv.i4.to.i1($ld.u1(m, p)));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr, v:bv32 :: { $st.i1(m, p, v) }
  $st.i1(m, p, v) == $_set_byte(m, $base(p), $offset(p), v[8:0]));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr, v:bv32 :: { $st.i2(m, p, v) }
  $st.i2(m, p, v) == 
    $_set_byte($_set_byte(m, $base(p), $offset(p), v[8:0]), $base(p), $add.i8($offset(p), 1bv64), v[16:8]));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr, v:bv32 :: { $st.i4(m, p, v) }
  $st.i4(m, p, v) == 
    $_set_byte(
      $_set_byte(
        $_set_byte(
          $_set_byte(m, 
            $base(p), $offset(p), v[8:0]), 
          $base(p), $add.i8($offset(p), 1bv64), v[16:8]),
        $base(p), $add.i8($offset(p), 2bv64), v[24:16]),
      $base(p), $add.i8($offset(p), 3bv64), v[32:24]));

axiom {:ignore "bvInt"} (forall m:$mem, p:$ptr, v:bv64 :: { $st.i8(m, p, v) }
  $st.i8(m, p, v) == 
    $_set_byte(
      $_set_byte(
        $_set_byte(
          $_set_byte(
            $_set_byte(
              $_set_byte(
                $_set_byte(
                  $_set_byte(m, 
                    $base(p), $offset(p), v[8:0]), 
                  $base(p), $add.i8($offset(p), 1bv64), v[16:8]),
                $base(p), $add.i8($offset(p), 2bv64), v[24:16]),
              $base(p), $add.i8($offset(p), 3bv64), v[32:24]),
            $base(p), $add.i8($offset(p), 4bv64), v[40:32]), 
          $base(p), $add.i8($offset(p), 5bv64), v[48:40]),
        $base(p), $add.i8($offset(p), 6bv64), v[56:48]),
      $base(p), $add.i8($offset(p), 7bv64), v[64:56]));



axiom {:ignore "bvInt"} (forall v:bv32 :: { $conv.i4.to.i1(v) } $conv.i4.to.i1(v) == $_sign_extend.8.32(v[8:0]));
axiom {:ignore "bvInt"} (forall v:bv32 :: { $conv.i4.to.i2(v) } $conv.i4.to.i2(v) == $_sign_extend.16.32(v[16:0]));
axiom {:ignore "bvInt"} (forall v:bv64 :: { $conv.i8.to.i1(v) } $conv.i8.to.i1(v) == $_sign_extend.8.32(v[8:0]));
axiom {:ignore "bvInt"} (forall v:bv64 :: { $conv.i8.to.i2(v) } $conv.i8.to.i2(v) == $_sign_extend.16.32(v[16:0]));

axiom {:ignore "bvInt"} (forall v:bv32 :: { $conv.i4.to.i8(v) } $conv.i4.to.i8(v) == $_sign_extend.32.64(v));
axiom {:ignore "bvInt"} (forall v:bv32 :: { $conv.i4.to.u8(v) } $conv.i4.to.u8(v) == 0bv32 ++ v);
axiom {:ignore "bvInt"} (forall v:bv64 :: { $conv.i8.to.i4(v) } $conv.i8.to.i4(v) == v[32:0]);
axiom {:ignore "bvInt"} (forall v:bv32 :: { $conv.i4.to.u1(v) } $conv.i4.to.u1(v) == 0bv24 ++ v[8:0]);
axiom {:ignore "bvInt"} (forall v:bv32 :: { $conv.i4.to.u2(v) } $conv.i4.to.u2(v) == 0bv16 ++ v[16:0]);
axiom {:ignore "bvInt"} (forall v:bv64 :: { $conv.i8.to.u1(v) } $conv.i8.to.u1(v) == 0bv24 ++ v[8:0]);
axiom {:ignore "bvInt"} (forall v:bv64 :: { $conv.i8.to.u2(v) } $conv.i8.to.u2(v) == 0bv16 ++ v[16:0]);

// -----------------------------------------------------------------------
// BV-->int memory model
// -----------------------------------------------------------------------

function $_ld.i(m:$mem, p:$ptr, len:int) returns(int);
function $_st.i(m:$mem, p:$ptr, len:int, v:int) returns($mem);
function $_shl(x:int, y:int) returns(int);
function $_shr(x:int, y:int) returns(int);
function $_or(x:int, y:int) returns(int);
function $_xor(x:int, y:int) returns(int);
function $_and(x:int, y:int) returns(int);
function $_not(x:int) returns(int);

function $_ioffset(p:$ptr) returns(int);

function {:bvint "id"} $_int.to.bv32(v:int) returns(bv32);
function {:bvint "id"} $_int.to.bv64(v:int) returns(bv64);
function {:bvint "id"} $_bv32.to.int(v:bv32) returns(int);
function {:bvint "id"} $_bv64.to.int(v:bv64) returns(int);

axiom {:ignore "bvDefSem"} (forall p:$ptr :: { $_ioffset(p) } $_ioffset(p) == $_bv64.to.int($offset(p)));

axiom {:ignore "bvDefSem"} (forall m:$mem, len:int, v:int, p:$ptr ::
  $_ld.i($_st.i(m, p, len, v), p, len) == v);

axiom {:ignore "bvDefSem"} (forall m:$mem, l1:int, l2:int, v:int, p1:$ptr, p2:$ptr ::
  ($base(p1) != $base(p2) || $_ioffset(p1) + l1 <= $_ioffset(p2) || $_ioffset(p2) + l2 <= $_ioffset(p1)) ==>
    $_ld.i($_st.i(m, p1, l1, v), p2, l2) == $_ld.i(m, p2, l2));

// Arithmetic axioms for int mapping
axiom {:ignore "bvDefSem"} (forall i: int :: { $_shl(i, 0) } $_shl(i, 0) == i);
axiom {:ignore "bvDefSem"} (forall i: int, j: int :: { $_shl(i, j) } 1 <= j ==> $_shl(i, j) == $_shl(i, j - 1) * 2);
axiom {:ignore "bvDefSem"} (forall i: int :: { $_shr(i, 0) } $_shr(i, 0) == i);
axiom {:ignore "bvDefSem"} (forall i: int, j: int :: { $_shr(i, j) } 1 <= j ==> 2 * $_shr(i, j) <= $_shr(i, j - 1) && $_shr(i, j - 1) <= 2 * $_shr(i, j) + 1);

axiom {:ignore "bvDefSem"} (forall i: int, j: int :: { i / j }  i > 0 && j > 0 ==> i - j < (i / j) * j && (i / j) * j <= i);

// from Spec# prelude, needs review
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { x % y } { x / y } x % y == x - x / y * y);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { x % y } 0 <= x && 0 < y ==> 0 <= x % y && x % y < y);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { x % y } 0 <= x && y < 0 ==> 0 <= x % y && x % y < 0 - y);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { x % y } x <= 0 && 0 < y ==> 0 - y < x % y && x % y <= 0);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { x % y } x <= 0 && y < 0 ==> y < x % y && x % y <= 0);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { (x + y) % y } 0 <= x && 0 <= y ==> (x + y) % y == x % y);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { (y + x) % y } 0 <= x && 0 <= y ==> (y + x) % y == x % y);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { (x - y) % y } 0 <= x - y && 0 <= y ==> (x - y) % y == x % y);
axiom {:ignore "bvDefSem"} (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b ==> a + d <= b);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { $_and(x, y) } 0 <= x || 0 <= y ==> 0 <= $_and(x, y));
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { $_or(x, y) } 0 <= x && 0 <= y ==> 0 <= $_or(x, y) && $_or(x, y) <= x + y);

axiom {:ignore "bvDefSem"} (forall x: int :: { $_or(x, $_not(x)) }  $_or(x, $_not(x)) == $_not(0));
axiom {:ignore "bvDefSem"} (forall x: int :: { $_and(x, $_not(x)) }  $_and(x, $_not(x)) == 0);
axiom {:ignore "bvDefSem"} (forall x: int :: { $_or(x, 0) }  $_or(x, 0) == x);
axiom {:ignore "bvDefSem"} (forall x: int :: { $_or(x, $_not(0)) }  $_or(x, $_not(0)) == $_not(0));
axiom {:ignore "bvDefSem"} (forall x: int :: { $_and(x, 0) }  $_and(x, 0) == 0);
axiom {:ignore "bvDefSem"} (forall x: int :: { $_and(x, $_not(0)) }  $_and(x, $_not(0)) == x);
axiom {:ignore "bvDefSem"} (forall x: int :: { $_xor(x, 0) }  $_xor(x, 0) == x);
axiom {:ignore "bvDefSem"} (forall x: int :: { $_xor(x, $_not(0)) }  $_xor(x, $_not(0)) == $_not(x));
axiom {:ignore "bvDefSem"} (forall x: int :: { $_not($_not(x)) }  $_not($_not(x)) == x);
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { $_or(x, y) } $_or(x, y) == $_or(y, x));
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { $_xor(x, y) } $_xor(x, y) == $_xor(y, x));
axiom {:ignore "bvDefSem"} (forall x: int, y: int :: { $_and(x, y) } $_and(x, y) == $_and(y, x));

axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem :: $ld.i1(m, p) == $_int.to.bv32($_ld.i(m, p, 1)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem, v:bv32 :: $st.i1(m, p, v) == $_st.i(m, p, 1, $_bv32.to.int(v)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem :: $ld.u1(m, p) == $_int.to.bv32($_ld.i(m, p, 1)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem :: $ld.i2(m, p) == $_int.to.bv32($_ld.i(m, p, 2)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem, v:bv32 :: $st.i2(m, p, v) == $_st.i(m, p, 2, $_bv32.to.int(v)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem :: $ld.u2(m, p) == $_int.to.bv32($_ld.i(m, p, 2)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem :: $ld.i4(m, p) == $_int.to.bv32($_ld.i(m, p, 4)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem, v:bv32 :: $st.i4(m, p, v) == $_st.i(m, p, 4, $_bv32.to.int(v)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem :: $ld.i8(m, p) == $_int.to.bv64($_ld.i(m, p, 8)));
axiom {:ignore "bvDefSem"} (forall p:$ptr, m:$mem, v:bv64 :: $st.i8(m, p, v) == $_st.i(m, p, 8, $_bv64.to.int(v)));


// -----------------------------------------------------------------------
// Utilities
// -----------------------------------------------------------------------

function $ite.i4(cond:bool, then:bv32, else_:bv32) returns(bv32);
function $ite.i8(cond:bool, then:bv64, else_:bv64) returns(bv64);
function $ite.ptr(cond:bool, then:$ptr, else_:$ptr) returns($ptr);

/*
axiom (forall cond:bool, then:bv32, else_:bv32 :: 
  cond ==> $ite.i4(cond, then, else_) == then);
axiom (forall cond:bool, then:bv32, else_:bv32 :: 
  !cond ==> $ite.i4(cond, then, else_) == else_);

axiom (forall cond:bool, then:bv64, else_:bv64 :: 
  cond ==> $ite.i8(cond, then, else_) == then);
axiom (forall cond:bool, then:bv64, else_:bv64 :: 
  !cond ==> $ite.i8(cond, then, else_) == else_);

axiom (forall cond:bool, then:$ptr, else_:$ptr :: 
  cond ==> $ite.ptr(cond, then, else_) == then);
axiom (forall cond:bool, then:$ptr, else_:$ptr :: 
  !cond ==> $ite.ptr(cond, then, else_) == else_);
*/

// -----------------------------------------------------------------------
// Conversions
// -----------------------------------------------------------------------

function {:bvint "id"} $conv.i4.to.i1(v:bv32) returns(bv32); 
function {:bvint "id"} $conv.i4.to.i2(v:bv32) returns(bv32);
function {:bvint "id"} $conv.i8.to.i1(v:bv64) returns(bv32); 
function {:bvint "id"} $conv.i8.to.i2(v:bv64) returns(bv32);
function {:bvint "id"} $conv.i4.to.i8(v:bv32) returns(bv64);
function {:bvint "id"} $conv.i4.to.u8(v:bv32) returns(bv64);
function {:bvint "id"} $conv.i8.to.i4(v:bv64) returns(bv32);
function {:bvint "id"} $conv.i4.to.u1(v:bv32) returns(bv32);
function {:bvint "id"} $conv.i4.to.u2(v:bv32) returns(bv32);
function {:bvint "id"} $conv.i8.to.u1(v:bv64) returns(bv32);
function {:bvint "id"} $conv.i8.to.u2(v:bv64) returns(bv32);

function $conv.ptr.to.i8(p:$ptr) returns(bv64);
function $_conv.base.to.i8(p:ref) returns(bv64);
function $conv.i8.to.ptr(p:bv64) returns($ptr);

function $conv.bool.to.i4(v:bool) returns(bv32);
function $conv.i4.to.bool(v:bv32) returns(bool);

// TODO: use patterns here?
axiom (forall p:$ptr :: $conv.i8.to.ptr($conv.ptr.to.i8(p)) == p);
axiom (forall p:bv64 :: $conv.ptr.to.i8($conv.i8.to.ptr(p)) == p);

axiom (forall p:$ptr :: $conv.ptr.to.i8(p) == $add.i8($_conv.base.to.i8($base(p)), $offset(p)));
// TODO what about i4?

axiom ($conv.ptr.to.i8($ldnull) == 0bv64);
axiom ($conv.i8.to.ptr(0bv64) == $ldnull);

axiom (forall m:$mem, p:$ptr :: { $ld.ptr(m, p) } $ld.ptr(m, p) == $conv.i8.to.ptr($ld.i8(m, p)));
axiom (forall m:$mem, p:$ptr, v:$ptr :: { $st.ptr(m, p, v) } $st.ptr(m, p, v) == $st.i8(m, p, $conv.ptr.to.i8(v)));

axiom $conv.bool.to.i4(true) == 1bv32;
axiom $conv.bool.to.i4(false) == 0bv32;
axiom $conv.i4.to.bool(0bv32) == false;
axiom (forall v:bv32 :: v != 0bv32 ==> $conv.i4.to.bool(v) == true);

// -----------------------------------------------------------------------
// Arithetmic
// -----------------------------------------------------------------------

const $min.u1:bv32;
axiom $min.u1 == 0bv32;
const $max.u1:bv32;
axiom $max.u1 == 255bv32;
const $min.i1:bv32;
axiom $min.i1 == $neg.i4(128bv32);
const $max.i1:bv32;
axiom $max.i1 == 127bv32;

const $min.u2:bv32;
axiom $min.u2 == 0bv32;
const $max.u2:bv32;
axiom $max.u2 == 65535bv32;
const $min.i2:bv32;
axiom $min.i2 == $neg.i4(32768bv32);
const $max.i2:bv32;
axiom $max.i2 == 32767bv32;

const $min.u4:bv32;
axiom $min.u4 == 0bv32;
const $max.u4:bv32;
axiom $max.u4 == 4294967295bv32;
const $min.i4:bv32;
axiom $min.i4 == $neg.i4(2147483648bv32);
const $max.i4:bv32;
axiom $max.i4 == 2147483647bv32;

const $min.u8:bv64;
axiom $min.u8 == 0bv64;
const $max.u8:bv64;
axiom $max.u8 == 18446744073709551615bv64;
const $min.i8:bv64;
axiom $min.i8 == $neg.i8(9223372036854775808bv64);
const $max.i8:bv64;
axiom $max.i8 == 9223372036854775807bv64;

function {:bvbuiltin "bvadd"} {:bvint "+"} $add.i4(x:bv32, y:bv32) returns(bv32);
function $check.add.i4(x:bv32, y:bv32) returns(bool);
function $check.add.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvadd"} {:bvint "+"} $add.i8(x:bv64, y:bv64) returns(bv64);
function $check.add.i8(x:bv64, y:bv64) returns(bool);
function $check.add.u8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvsub"} {:bvint "-"} $sub.i4(x:bv32, y:bv32) returns(bv32);
function $check.sub.i4(x:bv32, y:bv32) returns(bool);
function $check.sub.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvsub"} {:bvint "-"} $sub.i8(x:bv64, y:bv64) returns(bv64);
function $check.sub.i8(x:bv64, y:bv64) returns(bool);
function $check.sub.u8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvmul"} {:bvint "*"} $mul.i4(x:bv32, y:bv32) returns(bv32);
function $check.mul.i4(x:bv32, y:bv32) returns(bool);
function $check.mul.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvmul"} {:bvint "*"} $mul.i8(x:bv64, y:bv64) returns(bv64);
function $check.mul.i8(x:bv64, y:bv64) returns(bool);
function $check.mul.u8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvand"} {:bvint "$_and"} $and.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvand"} {:bvint "$_and"} $and.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvor"} {:bvint "$_or"} $or.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvor"} {:bvint "$_or"} $or.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvxor"} {:bvint "$_xor"} $xor.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvxor"} {:bvint "$_xor"} $xor.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvshl"} {:bvint "$_shl"} $shl.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvshl"} {:bvint "$_shl"} $shl.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvsdiv"} {:bvint "/"} $div.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} {:bvint "/"} $div.u4(x:bv32, y:bv32) returns(bv32);
function $check.div.i4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvsdiv"} {:bvint "/"} $div.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} {:bvint "/"} $div.u8(x:bv64, y:bv64) returns(bv64);
function $check.div.i8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvsrem"} {:bvint "%"} $rem.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvurem"} {:bvint "%"} $rem.u4(x:bv32, y:bv32) returns(bv32);
function $check.rem.i4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvsrem"} {:bvint "%"} $rem.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvurem"} {:bvint "%"} $rem.u8(x:bv64, y:bv64) returns(bv64);
function $check.rem.i8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvashr"} {:bvint "$_shr"} $shr.i4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} {:bvint "$_shr"} $shr.u4(x:bv32, y:bv32) returns(bv32);
function {:bvbuiltin "bvashr"} {:bvint "$_shr"} $shr.i8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} {:bvint "$_shr"} $shr.u8(x:bv64, y:bv64) returns(bv64);
function {:bvbuiltin "bvneg"} {:bvint "- 0"} $neg.i4(x:bv32) returns(bv32);
function {:bvbuiltin "bvneg"} {:bvint "- 0"} $neg.i8(x:bv64) returns(bv64);
function {:bvbuiltin "bvnot"} {:bvint "$_not"} $not.i4(x:bv32) returns(bv32);
function {:bvbuiltin "bvnot"} {:bvint "$_not"} $not.i8(x:bv64) returns(bv64);
function {:bvbuiltin "bvsgt"} {:bvint ">"} $cgt.i4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvugt"} {:bvint ">"} $cgt.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvsgt"} {:bvint ">"} $cgt.i8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvugt"} {:bvint ">"} $cgt.u8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvslt"} {:bvint "<"} $clt.i4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvult"} {:bvint "<"} $clt.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvslt"} {:bvint "<"} $clt.i8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvult"} {:bvint "<"} $clt.u8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvsge"} {:bvint ">="} $cge.i4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvuge"} {:bvint ">="} $cge.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvsge"} {:bvint ">="} $cge.i8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvuge"} {:bvint ">="} $cge.u8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvsle"} {:bvint "<="} $cle.i4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvule"} {:bvint "<="} $cle.u4(x:bv32, y:bv32) returns(bool);
function {:bvbuiltin "bvsle"} {:bvint "<="} $cle.i8(x:bv64, y:bv64) returns(bool);
function {:bvbuiltin "bvule"} {:bvint "<="} $cle.u8(x:bv64, y:bv64) returns(bool);

function $_inrange.i1(bv32) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv32 :: { $_inrange.i1(x) } $_inrange.i1(x) <==> $cle.i4($min.i1, x) && $cle.i4(x, $max.i1));

function $_inrange.u1(bv32) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv32 :: { $_inrange.u1(x) } $_inrange.u1(x) <==> $cle.u4($min.u1, x) && $cle.u4(x, $max.u1));

function $_inrange.i2(bv32) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv32 :: { $_inrange.i2(x) } $_inrange.i2(x) <==> $cle.i4($min.i2, x) && $cle.i4(x, $max.i2));

function $_inrange.u2(bv32) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv32 :: { $_inrange.u2(x) } $_inrange.u2(x) <==> $cle.u4($min.u2, x) && $cle.u4(x, $max.u2));

function $_inrange.i4(bv32) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv32 :: { $_inrange.i4(x) } $_inrange.i4(x) <==> $cle.i4($min.i4, x) && $cle.i4(x, $max.i4));

function $_inrange.u4(bv32) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv32 :: { $_inrange.u4(x) } $_inrange.u4(x) <==> $cle.u4($min.u4, x) && $cle.u4(x, $max.u4));

function $_inrange.i8(bv64) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv64 :: { $_inrange.i8(x) } $_inrange.i8(x) <==> $cle.i8($min.i8, x) && $cle.i8(x, $max.i8));

function $_inrange.u8(bv64) returns(bool);
axiom {:ignore "bvDefSem"} (forall x:bv64 :: { $_inrange.u8(x) } $_inrange.u8(x) <==> $cle.u8($min.u8, x) && $cle.u8(x, $max.u8));
axiom {:ignore "bvDefSem"} (forall x:bv32, y:bv32 :: { $check.add.i4(x, y) } $check.add.i4(x, y) <==> $_inrange.i4($add.i4(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv32, y:bv32 :: { $check.add.u4(x, y) } $check.add.u4(x, y) <==> $_inrange.u4($add.i4(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv64, y:bv64 :: { $check.add.i8(x, y) } $check.add.i8(x, y) <==> $_inrange.i8($add.i8(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv64, y:bv64 :: { $check.add.u8(x, y) } $check.add.u8(x, y) <==> $_inrange.u8($add.i8(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv32, y:bv32 :: { $check.sub.i4(x, y) } $check.sub.i4(x, y) <==> $_inrange.i4($sub.i4(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv32, y:bv32 :: { $check.sub.u4(x, y) } $check.sub.u4(x, y) <==> $_inrange.u4($sub.i4(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv64, y:bv64 :: { $check.sub.i8(x, y) } $check.sub.i8(x, y) <==> $_inrange.i8($sub.i8(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv64, y:bv64 :: { $check.sub.u8(x, y) } $check.sub.u8(x, y) <==> $_inrange.u8($sub.i8(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv32, y:bv32 :: { $check.mul.i4(x, y) } $check.mul.i4(x, y) <==> $_inrange.i4($mul.i4(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv32, y:bv32 :: { $check.mul.u4(x, y) } $check.mul.u4(x, y) <==> $_inrange.u4($mul.i4(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv64, y:bv64 :: { $check.mul.i8(x, y) } $check.mul.i8(x, y) <==> $_inrange.i8($mul.i8(x, y)));
axiom {:ignore "bvDefSem"} (forall x:bv64, y:bv64 :: { $check.mul.u8(x, y) } $check.mul.u8(x, y) <==> $_inrange.u8($mul.i8(x, y)));

function $check.conv.i4.to.i1(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.i4.to.i1(x) } 
      $check.conv.i4.to.i1(x) <==> $cle.i4(($min.i1), x) && $cle.i4(x, ($max.i1)));

function $check.conv.i4.to.u1(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.i4.to.u1(x) } 
      $check.conv.i4.to.u1(x) <==> $cle.i4(($min.u1), x) && $cle.i4(x, ($max.u1)));

function $check.conv.i4.to.i2(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.i4.to.i2(x) } 
      $check.conv.i4.to.i2(x) <==> $cle.i4(($min.i2), x) && $cle.i4(x, ($max.i2)));

function $check.conv.i4.to.u2(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.i4.to.u2(x) } 
      $check.conv.i4.to.u2(x) <==> $cle.i4(($min.u2), x) && $cle.i4(x, ($max.u2)));

function $check.conv.i4.to.u4(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.i4.to.u4(x) } 
      $check.conv.i4.to.u4(x) <==> $cle.i4(0bv32, x));

function $check.conv.i4.to.u8(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.i4.to.u8(x) } 
      $check.conv.i4.to.u8(x) <==> $cle.i4(0bv32, x));

function $check.conv.u4.to.i1(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.u4.to.i1(x) } 
      $check.conv.u4.to.i1(x) <==> $cle.u4(x, ($max.i1)));

function $check.conv.u4.to.u1(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.u4.to.u1(x) } 
      $check.conv.u4.to.u1(x) <==> $cle.u4(x, ($max.u1)));

function $check.conv.u4.to.i2(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.u4.to.i2(x) } 
      $check.conv.u4.to.i2(x) <==> $cle.u4(x, ($max.i2)));

function $check.conv.u4.to.u2(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.u4.to.u2(x) } 
      $check.conv.u4.to.u2(x) <==> $cle.u4(x, ($max.u2)));

function $check.conv.u4.to.i4(bv32) returns(bool);
axiom (forall x:bv32 :: { $check.conv.u4.to.i4(x) } 
      $check.conv.u4.to.i4(x) <==> $cle.u4(x, ($max.i4)));

function $check.conv.i8.to.i1(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.i1(x) } 
      $check.conv.i8.to.i1(x) <==> $cle.i8($conv.i4.to.i8($min.i1), x) && $cle.i8(x, $conv.i4.to.i8($max.i1)));

function $check.conv.i8.to.u1(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.u1(x) } 
      $check.conv.i8.to.u1(x) <==> $cle.i8($conv.i4.to.u8($min.u1), x) && $cle.i8(x, $conv.i4.to.u8($max.u1)));

function $check.conv.i8.to.i2(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.i2(x) } 
      $check.conv.i8.to.i2(x) <==> $cle.i8($conv.i4.to.i8($min.i2), x) && $cle.i8(x, $conv.i4.to.i8($max.i2)));

function $check.conv.i8.to.u2(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.u2(x) } 
      $check.conv.i8.to.u2(x) <==> $cle.i8($conv.i4.to.u8($min.u2), x) && $cle.i8(x, $conv.i4.to.u8($max.u2)));

function $check.conv.i8.to.i4(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.i4(x) } 
      $check.conv.i8.to.i4(x) <==> $cle.i8($conv.i4.to.i8($min.i4), x) && $cle.i8(x, $conv.i4.to.i8($max.i4)));

function $check.conv.i8.to.u4(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.u4(x) } 
      $check.conv.i8.to.u4(x) <==> $cle.i8($conv.i4.to.u8($min.u4), x) && $cle.i8(x, $conv.i4.to.u8($max.u4)));

function $check.conv.i8.to.u8(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.i8.to.u8(x) } 
      $check.conv.i8.to.u8(x) <==> $cle.i8(0bv64, x));

function $check.conv.u8.to.i1(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.i1(x) } 
      $check.conv.u8.to.i1(x) <==> $cle.u8(x, $conv.i4.to.i8($max.i1)));

function $check.conv.u8.to.u1(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.u1(x) } 
      $check.conv.u8.to.u1(x) <==> $cle.u8(x, $conv.i4.to.u8($max.u1)));

function $check.conv.u8.to.i2(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.i2(x) } 
      $check.conv.u8.to.i2(x) <==> $cle.u8(x, $conv.i4.to.i8($max.i2)));

function $check.conv.u8.to.u2(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.u2(x) } 
      $check.conv.u8.to.u2(x) <==> $cle.u8(x, $conv.i4.to.u8($max.u2)));

function $check.conv.u8.to.i4(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.i4(x) } 
      $check.conv.u8.to.i4(x) <==> $cle.u8(x, $conv.i4.to.i8($max.i4)));

function $check.conv.u8.to.u4(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.u4(x) } 
      $check.conv.u8.to.u4(x) <==> $cle.u8(x, $conv.i4.to.u8($max.u4)));

function $check.conv.u8.to.i8(bv64) returns(bool);
axiom (forall x:bv64 :: { $check.conv.u8.to.i8(x) } 
      $check.conv.u8.to.i8(x) <==> $cle.u8(x, ($max.i8)));

axiom (forall x:bv32, y:bv32 :: { $check.div.i4(x, y) } $check.div.i4(x, y) <==> ! (x == $min.i4 && y == $neg.i4(1bv32)));
axiom (forall x:bv32, y:bv32 :: { $check.rem.i4(x, y) } $check.rem.i4(x, y) <==> ! (x == $min.i4 && y == $neg.i4(1bv32)));

axiom (forall x:bv64, y:bv64 :: { $check.div.i8(x, y) } $check.div.i8(x, y) <==> ! (x == $min.i8 && y == $neg.i8(1bv64)));
axiom (forall x:bv64, y:bv64 :: { $check.rem.i8(x, y) } $check.rem.i8(x, y) <==> ! (x == $min.i8 && y == $neg.i8(1bv64)));


// -----------------------------------------------------------------------
// malloc/free
// -----------------------------------------------------------------------

var $mem : $mem;
var $gmem : [$ptr,<x>name]x;

const unique $_size : <bv64>name;

function $valid(m:[$ptr,<x>name]x, p:$ptr, l:bv64) returns(bool);
// we cannot use array, as boogie/z3 does not support bv arrays
function $size(m:[$ptr,<x>name]x, p:ref) returns(bv64);
function $allocated(m:[$ptr,<x>name]x, p:$ptr) returns(bool);
function $is_fresh(oldalloc:[$ptr,<x>name]x, newalloc:[$ptr,<x>name]x, p:$ptr) returns(bool);
function $same_region(mdst:$mem, dst:$ptr, msrc:$mem, src:$ptr, len:bv64) returns(bool);
function $always_allocated(p:$ptr, sz:bv64) returns(bool);

// For writes(set) the postcondition is:
//   ensures $only_region_changed_or_new(set, old($gmem), old($mem), $mem);
//
// For reads(set) the postcondition is:
//   ensures $contains(##readsSet, set);
//
// For frees(p1;p2;...) the postcondition is:
//   ensures (forall r:ref :: { $size($gmem, r) }
//     $size($gmem, r) == $size(old($gmem), r) ||
//     $size(old($gmem), r) == 0bv64 ||
//     (r == $base(p1) && $offset(p1) == 0bv64) ||
//     (r == $base(p2) && $offset(p2) == 0bv64) ||
//     ...);
//
// The sets are constructed using $region, $union, $empty and $universe.

axiom (forall alloc:[$ptr,<x>name]x, p:$ptr, len:bv64 :: 
    { $valid(alloc, p, len) }
    $valid(alloc, p, len) <==> 
      p != $ldnull &&
      $cgt.u8(len, 0bv64) && $cge.u8($offset(p), 0bv64) && // for int model
      $cgt.u8($add.i8($offset(p), len), $offset(p)) &&
      $cle.u8($add.i8($offset(p), len), $size(alloc, $base(p))));

axiom (forall oldalloc:[$ptr,<x>name]x, newalloc:[$ptr,<x>name]x, p:$ptr :: { $is_fresh(oldalloc, newalloc, p) }
    $is_fresh(oldalloc, newalloc, p) <==>
      !$allocated(oldalloc, p) && $allocated(newalloc, p));

axiom (forall m:[$ptr,<x>name]x, p:ref :: { $size(m, p) }
  $size(m, p) == m[$_ptr(p, 0bv64), $_size]);

axiom (forall m:[$ptr,<x>name]x, p:$ptr :: { $allocated(m, p) }
  $allocated(m, p) <==> $size(m, $base(p)) != 0bv64);

// this one is here to help discharge false aliasing accustions between globals
// and freshly allocated memory
axiom (forall g:$ptr, sz:bv64 :: { $always_allocated(g, sz) }
  $always_allocated(g, sz) <==>
    (forall a:[$ptr,<x>name]x :: $allocated(a, g)) &&
    (forall a:[$ptr,<x>name]x :: $size(a, $base(g)) == sz));

procedure $malloc(size:bv64) returns (p:$ptr); 
         modifies $gmem;
         ensures p != $ldnull ==> 
            $base(p) != null &&
            $size(old($gmem), $base(p)) == 0bv64 &&
            $size($gmem, $base(p)) == size &&
            $offset(p) == 0bv64 &&
            (forall r:ref :: { $size($gmem, r) } 
             r != $base(p) ==> $size(old($gmem), r) == $size($gmem, r));
         ensures p == $ldnull ==> 
            old($gmem) == $gmem;
 
procedure $free(p:$ptr); 
         modifies $gmem;
         requires p == $ldnull || $size($gmem, $base(p)) != 0bv64; 
         ensures 
            p != $ldnull ==>
              $size($gmem, $base(p)) == 0bv64 &&
              (forall r:ref :: { $size($gmem, r) } 
               r != $base(p) ==> $size(old($gmem), r) == $size($gmem, r));
         ensures 
            p == $ldnull ==>
              old($gmem) == $gmem;

axiom (forall mdst:$mem, dst:$ptr, msrc:$mem, src:$ptr, len:bv64 ::
  { $same_region(mdst, dst, msrc, src, len) }
  $same_region(mdst, dst, msrc, src, len) <==>
    (forall p:$ptr :: { $ld.i1(mdst, p) }
      $contains($region(p, 1bv64), $region(dst, len)) ==> $ld.i1(mdst, p) == $ld.i1(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))) &&
    (forall p:$ptr :: { $ld.u1(mdst, p) }
      $contains($region(p, 1bv64), $region(dst, len)) ==> $ld.u1(mdst, p) == $ld.u1(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))) &&
    (forall p:$ptr :: { $ld.i2(mdst, p) }
      $contains($region(p, 2bv64), $region(dst, len)) ==> $ld.i2(mdst, p) == $ld.i2(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))) &&
    (forall p:$ptr :: { $ld.u2(mdst, p) }
      $contains($region(p, 2bv64), $region(dst, len)) ==> $ld.u2(mdst, p) == $ld.u2(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))) &&
    (forall p:$ptr :: { $ld.i4(mdst, p) }
      $contains($region(p, 4bv64), $region(dst, len)) ==> $ld.i4(mdst, p) == $ld.i4(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))) &&
    (forall p:$ptr :: { $ld.i8(mdst, p) }
      $contains($region(p, 8bv64), $region(dst, len)) ==> $ld.i8(mdst, p) == $ld.i8(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))) &&
    (forall p:$ptr :: { $ld.ptr(mdst, p) }
      $contains($region(p, 8bv64), $region(dst, len)) ==> $ld.ptr(mdst, p) == $ld.ptr(msrc, $add.ptr(src, $sub.ptr(p, dst), 1bv64))));


procedure $memmove(dest: $ptr, src: $ptr, noOfBytes: bv64);
  modifies $mem;
  requires $valid($gmem, dest, noOfBytes) && $valid($gmem, src, noOfBytes);
  ensures $same_region($mem, dest, old($mem), src, noOfBytes);
  ensures $only_region_changed($region(dest, noOfBytes), old($mem), $mem);

procedure $memcpy(dest: $ptr, src: $ptr, noOfBytes: bv64);
  modifies $mem;
  requires !$overlaps($region(dest, noOfBytes), $region(src, noOfBytes));
  requires $valid($gmem, dest, noOfBytes) && $valid($gmem, src, noOfBytes);
  ensures $same_region($mem, dest, old($mem), src, noOfBytes);
  ensures $only_region_changed($region(dest, noOfBytes), old($mem), $mem);

// -----------------------------------------------------------------------
// Writes clause handling
// -----------------------------------------------------------------------

// region is a set of memory locations
type $region;

function $region(p:$ptr, len:bv64) returns($region);
function $overlaps(r1:$region, r2:$region) returns(bool);
// check if big contains small
function $contains(small:$region, big:$region) returns(bool);
function $only_region_changed(r:$region, oldmem:$mem, newmem:$mem) returns(bool);
function $only_region_changed_or_new(r:$region, oldalloc:[$ptr,<x>name]x, oldmem:$mem, newmem:$mem) returns(bool);
function $nothing_in_region_changed(r:$region, oldmem:$mem, newmem:$mem) returns(bool);
function $alloc_grows(oldalloc:[$ptr,<x>name]x, newalloc:[$ptr,<x>name]x) returns(bool);

function $union(r1:$region, r2:$region) returns($region);
function $empty() returns($region);
function $universe() returns($region);

// NOTE $empty() is very different from $region(whatever, 0), for example $region(whatever, 0) is not contained in $empty()

axiom (forall r:$region :: !$overlaps($empty(), r));
axiom (forall r:$region :: !$overlaps(r, $empty()));
axiom (forall r:$region :: r != $empty() ==> $overlaps($universe(), r));
axiom (forall r:$region :: r != $empty() ==> $overlaps(r, $universe()));
axiom (forall r:$region :: $contains($empty(), r));
axiom (forall r:$region :: $contains(r, $empty()) ==> r == $empty());
axiom (forall r:$region :: $contains($universe(), r) ==> r == $universe());
axiom (forall r:$region :: $contains(r, $universe()));

// the triggers should do the structural induction
axiom (forall ptr1:$ptr, len1:bv64, ptr2:$ptr, len2:bv64 ::
  { $overlaps($region(ptr1, len1), $region(ptr2, len2)) }
  $overlaps($region(ptr1, len1), $region(ptr2, len2)) <==>
    $base(ptr1) == $base(ptr2) &&
      ((
          $cle.u8($offset(ptr1), $add.i8($offset(ptr1), len1)) &&
          $cle.u8($offset(ptr1), $offset(ptr2)) && 
          $clt.u8($offset(ptr2), $add.i8($offset(ptr1), len1)) 
       ) || ( 
          $cle.u8($offset(ptr2), $add.i8($offset(ptr2), len2)) &&
          $cle.u8($offset(ptr2), $offset(ptr1)) && 
          $clt.u8($offset(ptr1), $add.i8($offset(ptr2), len2)) 
       ) || 
         (
          $cgt.u8($offset(ptr1), $add.i8($offset(ptr1), len1)) &&
          ( $cle.u8($offset(ptr2), $add.i8($offset(ptr1), len1)) ||
            $cge.u8($add.i8($offset(ptr2), len2), $offset(ptr1))
          ))
         ||
         (
          $cgt.u8($offset(ptr2), $add.i8($offset(ptr2), len2)) &&
          ( $cle.u8($offset(ptr1), $add.i8($offset(ptr2), len2)) ||
            $cge.u8($add.i8($offset(ptr1), len1), $offset(ptr2))
          ))
       ));

axiom (forall r1:$region, r2:$region, r3:$region ::
  { $overlaps($union(r1, r2), r3) }
  $overlaps($union(r1, r2), r3) <==> $overlaps(r1, r3) || $overlaps(r2, r3));

axiom (forall r1:$region, r2:$region, r3:$region ::
  { $overlaps(r3, $union(r1, r2)) }
  $overlaps(r3, $union(r1, r2)) <==> $overlaps(r3, r1) || $overlaps(r3, r2));

axiom (forall big:$ptr, bigl:bv64, small:$ptr, smalll:bv64 ::
  { $contains($region(small, smalll), $region(big, bigl)) }
  $contains($region(small, smalll), $region(big, bigl)) <==>
    $base(big) == $base(small) &&
    $cle.u8($offset(big), $offset(small)) && 
    $cle.u8($offset(small), $_end(big, bigl)) &&
    $cle.u8($offset(big), $_end(small, smalll)) && 
    $cle.u8($_end(small, smalll), $_end(big, bigl)));

axiom (forall r1:$region, r2:$region, r3:$region ::
  { $contains(r1, $union(r2, r3)) }
  $contains(r1, $union(r2, r3)) <==> $contains(r1, r2) || $contains(r1, r3));

axiom (forall r1:$region, r2:$region, r3:$region ::
  { $contains($union(r1, r2), r3) }
  $contains($union(r1, r2), r3) <==> $contains(r1, r3) && $contains(r2, r3));

axiom (forall r:$region, oldmem:$mem, newmem:$mem ::
  { $only_region_changed(r, oldmem, newmem) }
  $only_region_changed(r, oldmem, newmem) <==>

    (forall p:$ptr :: { $ld.i1(oldmem, p) } { $ld.i1(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 1bv64), r) || $ld.i1(oldmem, p) == $ld.i1(newmem, p)) &&
    (forall p:$ptr :: { $ld.u1(oldmem, p) } { $ld.u1(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 1bv64), r) || $ld.u1(oldmem, p) == $ld.u1(newmem, p)) &&
    (forall p:$ptr :: { $ld.i2(oldmem, p) } { $ld.i2(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 2bv64), r) || $ld.i2(oldmem, p) == $ld.i2(newmem, p)) &&
    (forall p:$ptr :: { $ld.u2(oldmem, p) } { $ld.u2(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 2bv64), r) || $ld.u2(oldmem, p) == $ld.u2(newmem, p)) &&
    (forall p:$ptr :: { $ld.i4(oldmem, p) } { $ld.i4(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 4bv64), r) || $ld.i4(oldmem, p) == $ld.i4(newmem, p)) &&
    (forall p:$ptr :: { $ld.i8(oldmem, p) } { $ld.i8(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 8bv64), r) || $ld.i8(oldmem, p) == $ld.i8(newmem, p)) &&
    (forall p:$ptr :: { $ld.ptr(oldmem, p) } { $ld.ptr(newmem, p) } // TODO maybe we want only newmem?
      $overlaps($region(p, 8bv64), r) || $ld.ptr(oldmem, p) == $ld.ptr(newmem, p)));


axiom (forall r:$region, oldalloc:[$ptr,<x>name]x, oldmem:$mem, newmem:$mem ::
  { $only_region_changed_or_new(r, oldalloc, oldmem, newmem) }
  $only_region_changed_or_new(r, oldalloc, oldmem, newmem) <==>

    (forall p:$ptr :: { $ld.i1(oldmem, p) } { $ld.i1(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 1bv64), r) || $ld.i1(oldmem, p) == $ld.i1(newmem, p)) &&
    (forall p:$ptr :: { $ld.u1(oldmem, p) } { $ld.u1(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 1bv64), r) || $ld.u1(oldmem, p) == $ld.u1(newmem, p)) &&
    (forall p:$ptr :: { $ld.i2(oldmem, p) } { $ld.i2(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 2bv64), r) || $ld.i2(oldmem, p) == $ld.i2(newmem, p)) &&
    (forall p:$ptr :: { $ld.u2(oldmem, p) } { $ld.u2(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 2bv64), r) || $ld.u2(oldmem, p) == $ld.u2(newmem, p)) &&
    (forall p:$ptr :: { $ld.i4(oldmem, p) } { $ld.i4(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 4bv64), r) || $ld.i4(oldmem, p) == $ld.i4(newmem, p)) &&
    (forall p:$ptr :: { $ld.i8(oldmem, p) } { $ld.i8(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 8bv64), r) || $ld.i8(oldmem, p) == $ld.i8(newmem, p)) &&
    (forall p:$ptr :: { $ld.ptr(oldmem, p) } { $ld.ptr(newmem, p) } // TODO maybe we want only newmem?
      !$allocated(oldalloc, p) || $overlaps($region(p, 8bv64), r) || $ld.ptr(oldmem, p) == $ld.ptr(newmem, p)));


axiom (forall r:$region, oldmem:$mem, newmem:$mem ::
  { $nothing_in_region_changed(r, oldmem, newmem) }
  $nothing_in_region_changed(r, oldmem, newmem) <==>

    (forall p:$ptr :: { $ld.i1(oldmem, p) } { $ld.i1(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 1bv64), r) || $ld.i1(oldmem, p) == $ld.i1(newmem, p)) &&
    (forall p:$ptr :: { $ld.u1(oldmem, p) } { $ld.u1(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 1bv64), r) || $ld.u1(oldmem, p) == $ld.u1(newmem, p)) &&
    (forall p:$ptr :: { $ld.i2(oldmem, p) } { $ld.i2(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 2bv64), r) || $ld.i2(oldmem, p) == $ld.i2(newmem, p)) &&
    (forall p:$ptr :: { $ld.u2(oldmem, p) } { $ld.u2(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 2bv64), r) || $ld.u2(oldmem, p) == $ld.u2(newmem, p)) &&
    (forall p:$ptr :: { $ld.i4(oldmem, p) } { $ld.i4(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 4bv64), r) || $ld.i4(oldmem, p) == $ld.i4(newmem, p)) &&
    (forall p:$ptr :: { $ld.i8(oldmem, p) } { $ld.i8(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 8bv64), r) || $ld.i8(oldmem, p) == $ld.i8(newmem, p)) &&
    (forall p:$ptr :: { $ld.ptr(oldmem, p) } { $ld.ptr(newmem, p) } // TODO maybe we want only newmem?
      !$contains($region(p, 8bv64), r) || $ld.ptr(oldmem, p) == $ld.ptr(newmem, p)));



axiom (forall oldalloc:[$ptr,<x>name]x, newalloc:[$ptr,<x>name]x ::
  { $alloc_grows(oldalloc, newalloc) }
  $alloc_grows(oldalloc, newalloc) <==>
    (forall p:ref :: { $size(newalloc, p) }
      $size(oldalloc, p) == 0bv64 || $size(oldalloc, p) == $size(newalloc, p)));


// -----------------------------------------------------------------------
// That`s all folks!
// -----------------------------------------------------------------------


procedure x(a : bv64, b: bv64)
{
  block1 : return;
}

procedure a(a : bv32, b: bv32)
{
  block1 : 
     // OK:
     assert a == a;
     assert a[32:16] ++ a[16:0] == a;
     assert 0bv32 != 1bv32;
     // Error:
     assert $add.i4(a, b) == $add.i4(b, a);
     assert $and.i4(a, b) == $and.i4(b, a);
     assert $add.i4(a, 0bv32) == a;
     return;
}

procedure b(a : bv64, b: bv64)
{
  block1 : 
     assert a == a;
     assert a[64:16] ++ a[16:0] == a;
     assert $add.i8(a, b) == $add.i8(b, a);
     assert $and.i8(a, b) == $and.i8(b, a);
     return;
}

// Example usage of the memory model:
procedure foo()
  modifies $mem, $gmem;
{
   var p :$ptr;
   var q :bv32;

   block1:

      call p := $malloc(8bv64);

      if (p == $ldnull) { return; }

      assert $valid($gmem, p, 4bv64);
      
      $mem := $st.i1($mem, p, 42bv32);
      q := $ld.u1($mem, p);
      assert q == 42bv32;


      p := $add.ptr(p, 4bv64, 1bv64);
      assert $valid($gmem, p, 4bv64);
      $mem := $st.i4($mem, p, $add.i4(q, 42bv32));
      q := $ld.i4($mem, p);
      assert q == 84bv32;

      call $free(p);

      return;
}

procedure mem_model(mem:$mem, p:$ptr, a:bv32, b:bv64)
{
  assert $ld.i4($st.i4(mem, p, a), p) == a;
  assert $ld.i2($st.i2(mem, p, a), p)[16:0] == a[16:0];
  return;
}
