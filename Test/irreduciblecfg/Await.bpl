// RUN: %parallel-boogie "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L: Boogie program verifier finished with 1 verified, 0 errors

var new: int;
procedure await_eq_add(val : int)
    modifies new;
    ensures val == old(val);
    ensures (new == old(new) + val);
{
    var x : int;
    var tmp : bool;
    assume tmp == true;
    B: 
        havoc x;
        if (x == val) {
            goto E;
        }
        else {
            goto C;
        }
    C: 
        if (tmp == true) {
            havoc x;
        }
        goto D;
    D: 
        if (x != val) {
            goto C;
        }
        else {
            goto E;
        }
    E:
        havoc tmp;
        if (tmp == true) {
            new := new + x;
            goto G;
        }
        else {
            goto C;
        }
    G:
}