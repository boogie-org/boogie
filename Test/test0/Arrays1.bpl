// RUN: %boogie -noVerify "%s" | %OutputCheck "%s"
var Q: [int,int][int]int;

procedure P()
{
  var q: [int]int;

  start:
    // here's how to do it:
    q := Q[5,8];
    q[13] := 21;

    // CHECK-L: ${CHECKFILE_NAME}(${LINE:+1},11): Error: command assigns to a global variable that is not in the enclosing procedure's modifies clause: Q
    Q[5,8] := q;

    // not like this:
    // CHECK-L: ${CHECKFILE_NAME}(${LINE:+1},15): Error: command assigns to a global variable that is not in the enclosing procedure's modifies clause: Q
    Q[5,8][13] := 21;  // error: the updated array must be an identifier
    return;
}

// CHECK-L: 2 type checking errors detected in ${CHECKFILE_NAME}
