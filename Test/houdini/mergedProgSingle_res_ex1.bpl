// RUN: %boogie /nologo /contractInfer /inlineDepth:1 /printAssignment /noinfer  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var _v2.control_flag: int;

function _v2.control_UIF(arg_0: int, arg_1: int) : int;

procedure _v2.Eval(x: int) returns (result: int);
  modifies _v2.control_flag;
  free ensures {:io_dependency "control_flag", "control_flag", "x"} true;
  free ensures {:io_dependency "result", "x"} true;
  free ensures {:io_dependency "control_flag", "control_flag", "x"} true;
  free ensures {:io_dependency "result", "x"} true;



procedure _v2.Eval_loop_anon3_LoopHead(in_result: int, in_x: int) returns (out_result: int, out_x: int);
  modifies _v2.control_flag;
  free ensures {:io_dependency "control_flag", "control_flag", "in_x"} true;
  free ensures {:io_dependency "out_result", "in_result", "in_x"} true;
  free ensures {:io_dependency "out_x", "in_x"} true;
  free ensures {:io_dependency "control_flag", "control_flag", "in_x"} true;
  free ensures {:io_dependency "out_result", "in_result", "in_x"} true;
  free ensures {:io_dependency "out_x", "in_x"} true;



implementation _v2.Eval(x.1: int) returns (result: int)
{
  var x: int;

  anon0:
    x := x.1;
    result := 0;
    _v2.control_flag := 0;
    goto anon3_LoopHead;

  anon3_LoopHead:
    call result, x := _v2.Eval_loop_anon3_LoopHead(result, x);
    goto anon3_LoopHead_last;

  anon3_LoopHead_last:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} x > 0;
    _v2.control_flag := _v2.control_UIF(_v2.control_flag, 1);
    result := result + x;
    havoc result;
    x := x - 1;
    goto anon3_LoopBody_dummy;

  anon3_LoopBody_dummy:
    assume false;
    return;

  anon3_LoopDone:
    assume {:partition} 0 >= x;
    goto anon2;

  anon2:
    _v2.control_flag := _v2.control_UIF(_v2.control_flag, 2);
    return;
}



implementation _v2.Eval_loop_anon3_LoopHead(in_result: int, in_x: int) returns (out_result: int, out_x: int)
{

  entry:
    out_result, out_x := in_result, in_x;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} out_x > 0;
    _v2.control_flag := _v2.control_UIF(_v2.control_flag, 1);
    out_result := out_result + out_x;
    havoc out_result;
    out_x := out_x - 1;
    goto anon3_LoopBody_dummy;

  anon3_LoopBody_dummy:
    call out_result, out_x := _v2.Eval_loop_anon3_LoopHead(out_result, out_x);
    return;

  anon3_LoopDone:
    assume {:partition} 0 >= out_x;
    out_result, out_x := in_result, in_x;
    _v2.control_flag := old(_v2.control_flag);
    return;
}



var _v1.control_flag: int;

procedure _v1.Eval(x: int) returns (result: int);
  modifies _v1.control_flag;
  free ensures {:io_dependency "control_flag", "control_flag", "x"} true;
  free ensures {:io_dependency "result", "x"} true;
  free ensures {:io_dependency "control_flag", "control_flag", "x"} true;
  free ensures {:io_dependency "result", "x"} true;



procedure _v1.Eval_loop_anon3_LoopHead(in_result: int, in_x: int) returns (out_result: int, out_x: int);
  modifies _v1.control_flag;
  free ensures {:io_dependency "control_flag", "control_flag", "in_x"} true;
  free ensures {:io_dependency "out_result", "in_result", "in_x"} true;
  free ensures {:io_dependency "out_x", "in_x"} true;
  free ensures {:io_dependency "control_flag", "control_flag", "in_x"} true;
  free ensures {:io_dependency "out_result", "in_result", "in_x"} true;
  free ensures {:io_dependency "out_x", "in_x"} true;



implementation _v1.Eval(x.1: int) returns (result: int)
{
  var x: int;

  anon0:
    x := x.1;
    result := 0;
    _v1.control_flag := 0;
    goto anon3_LoopHead;

  anon3_LoopHead:
    call result, x := _v1.Eval_loop_anon3_LoopHead(result, x);
    goto anon3_LoopHead_last;

  anon3_LoopHead_last:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} x > 0;
    _v1.control_flag := _v2.control_UIF(_v1.control_flag, 1);
    result := result + x;
    x := x - 1;
    goto anon3_LoopBody_dummy;

  anon3_LoopBody_dummy:
    assume false;
    return;

  anon3_LoopDone:
    assume {:partition} 0 >= x;
    goto anon2;

  anon2:
    _v1.control_flag := _v2.control_UIF(_v1.control_flag, 2);
    return;
}



implementation _v1.Eval_loop_anon3_LoopHead(in_result: int, in_x: int) returns (out_result: int, out_x: int)
{

  entry:
    out_result, out_x := in_result, in_x;
    goto anon3_LoopHead;

  anon3_LoopHead:
    goto anon3_LoopDone, anon3_LoopBody;

  anon3_LoopBody:
    assume {:partition} out_x > 0;
    _v1.control_flag := _v2.control_UIF(_v1.control_flag, 1);
    out_result := out_result + out_x;
    out_x := out_x - 1;
    goto anon3_LoopBody_dummy;

  anon3_LoopBody_dummy:
    call out_result, out_x := _v1.Eval_loop_anon3_LoopHead(out_result, out_x);
    return;

  anon3_LoopDone:
    assume {:partition} 0 >= out_x;
    out_result, out_x := in_result, in_x;
    _v1.control_flag := old(_v1.control_flag);
    return;
}



function {:inline true} MS$_v1.Eval$_v2.Eval(_v1.x: int, 
    _v1.control_flag_old: int, 
    _v1.control_flag_: int, 
    _v1.result: int, 
    _v2.x: int, 
    _v2.control_flag_old: int, 
    _v2.control_flag_: int, 
    _v2.result: int)
   : bool
{
  true
}

const {:existential true} _houdini_Eval_control_flag_0: bool;

const {:existential true} _houdini_Eval_result_1: bool;

procedure MS_Check__v1.Eval___v2.Eval(_v1.x: int, _v2.x: int) returns (_v1.result: int, _v2.result: int);
  modifies _v1.control_flag, _v2.control_flag;
  ensures MS$_v1.Eval$_v2.Eval(_v1.x, 
  old(_v1.control_flag), 
  _v1.control_flag, 
  _v1.result, 
  _v2.x, 
  old(_v2.control_flag), 
  _v2.control_flag, 
  _v2.result);
  ensures _houdini_Eval_control_flag_0
   ==> 
  old(_v1.control_flag == _v2.control_flag && _v1.x == _v2.x)
   ==> _v1.control_flag == _v2.control_flag;
  ensures _houdini_Eval_result_1 ==> old(_v1.x == _v2.x) ==> _v1.result == _v2.result;



implementation MS_Check__v1.Eval___v2.Eval(_v1.x: int, _v2.x: int) returns (_v1.result: int, _v2.result: int)
{
  var inline$_v1.Eval$0$x: int;
  var inline$_v1.Eval$0$x.1: int;
  var inline$_v1.Eval$0$result: int;
  var inline$_v1.Eval$0$_v1.control_flag: int;
  var inline$_v2.Eval$0$x: int;
  var inline$_v2.Eval$0$x.1: int;
  var inline$_v2.Eval$0$result: int;
  var inline$_v2.Eval$0$_v2.control_flag: int;
  var _v1.Eval_loop_anon3_LoopHead_1_done: bool;
  var _v1.Eval_loop_anon3_LoopHead_in_1_0: int;
  var _v1.Eval_loop_anon3_LoopHead_in_1_1: int;
  var _v1.Eval_loop_anon3_LoopHead_in_1_2: int;
  var _v1.Eval_loop_anon3_LoopHead_out_1_0: int;
  var _v1.Eval_loop_anon3_LoopHead_out_1_1: int;
  var _v1.Eval_loop_anon3_LoopHead_out_1_2: int;
  var _v2.Eval_loop_anon3_LoopHead_2_done: bool;
  var _v2.Eval_loop_anon3_LoopHead_in_2_0: int;
  var _v2.Eval_loop_anon3_LoopHead_in_2_1: int;
  var _v2.Eval_loop_anon3_LoopHead_in_2_2: int;
  var _v2.Eval_loop_anon3_LoopHead_out_2_0: int;
  var _v2.Eval_loop_anon3_LoopHead_out_2_1: int;
  var _v2.Eval_loop_anon3_LoopHead_out_2_2: int;
  var store__0__v1.control_flag: int;
  var store__0__v2.control_flag: int;
  var out__v1.Eval_loop_anon3_LoopHead_out_1_0_0: int;
  var out__v1.Eval_loop_anon3_LoopHead_out_1_1_0: int;
  var out__v2.Eval_loop_anon3_LoopHead_out_2_0_0: int;
  var out__v2.Eval_loop_anon3_LoopHead_out_2_1_0: int;

  START:
    _v1.Eval_loop_anon3_LoopHead_1_done, _v2.Eval_loop_anon3_LoopHead_2_done := false, false;
    goto inline$_v1.Eval$0$Entry;

  inline$_v1.Eval$0$Entry:
    inline$_v1.Eval$0$x.1 := _v1.x;
    havoc inline$_v1.Eval$0$x, inline$_v1.Eval$0$result;
    inline$_v1.Eval$0$_v1.control_flag := _v1.control_flag;
    goto inline$_v1.Eval$0$anon0;

  inline$_v1.Eval$0$anon0:
    inline$_v1.Eval$0$x := inline$_v1.Eval$0$x.1;
    inline$_v1.Eval$0$result := 0;
    _v1.control_flag := 0;
    goto inline$_v1.Eval$0$anon3_LoopHead;

  inline$_v1.Eval$0$anon3_LoopHead:
    _v1.Eval_loop_anon3_LoopHead_in_1_0, _v1.Eval_loop_anon3_LoopHead_in_1_1, _v1.Eval_loop_anon3_LoopHead_in_1_2 := inline$_v1.Eval$0$result, inline$_v1.Eval$0$x, _v1.control_flag;
    call inline$_v1.Eval$0$result, inline$_v1.Eval$0$x := _v1.Eval_loop_anon3_LoopHead(inline$_v1.Eval$0$result, inline$_v1.Eval$0$x);
    _v1.Eval_loop_anon3_LoopHead_1_done := true;
    _v1.Eval_loop_anon3_LoopHead_out_1_0, _v1.Eval_loop_anon3_LoopHead_out_1_1, _v1.Eval_loop_anon3_LoopHead_out_1_2 := inline$_v1.Eval$0$result, inline$_v1.Eval$0$x, _v1.control_flag;
    goto inline$_v1.Eval$0$anon3_LoopHead_last;

  inline$_v1.Eval$0$anon3_LoopHead_last:
    goto inline$_v1.Eval$0$anon3_LoopDone, inline$_v1.Eval$0$anon3_LoopBody;

  inline$_v1.Eval$0$anon3_LoopBody:
    assume {:partition} inline$_v1.Eval$0$x > 0;
    _v1.control_flag := _v2.control_UIF(_v1.control_flag, 1);
    inline$_v1.Eval$0$result := inline$_v1.Eval$0$result + inline$_v1.Eval$0$x;
    inline$_v1.Eval$0$x := inline$_v1.Eval$0$x - 1;
    goto inline$_v1.Eval$0$anon3_LoopBody_dummy;

  inline$_v1.Eval$0$anon3_LoopBody_dummy:
    assume false;
    goto inline$_v1.Eval$0$Return;

  inline$_v1.Eval$0$anon3_LoopDone:
    assume {:partition} 0 >= inline$_v1.Eval$0$x;
    goto inline$_v1.Eval$0$anon2;

  inline$_v1.Eval$0$anon2:
    _v1.control_flag := _v2.control_UIF(_v1.control_flag, 2);
    goto inline$_v1.Eval$0$Return;

  inline$_v1.Eval$0$Return:
    assume true;
    assume true;
    assume true;
    assume true;
    _v1.result := inline$_v1.Eval$0$result;
    goto START$1;

  START$1:
    goto inline$_v2.Eval$0$Entry;

  inline$_v2.Eval$0$Entry:
    inline$_v2.Eval$0$x.1 := _v2.x;
    havoc inline$_v2.Eval$0$x, inline$_v2.Eval$0$result;
    inline$_v2.Eval$0$_v2.control_flag := _v2.control_flag;
    goto inline$_v2.Eval$0$anon0;

  inline$_v2.Eval$0$anon0:
    inline$_v2.Eval$0$x := inline$_v2.Eval$0$x.1;
    inline$_v2.Eval$0$result := 0;
    _v2.control_flag := 0;
    goto inline$_v2.Eval$0$anon3_LoopHead;

  inline$_v2.Eval$0$anon3_LoopHead:
    _v2.Eval_loop_anon3_LoopHead_in_2_0, _v2.Eval_loop_anon3_LoopHead_in_2_1, _v2.Eval_loop_anon3_LoopHead_in_2_2 := inline$_v2.Eval$0$result, inline$_v2.Eval$0$x, _v2.control_flag;
    call inline$_v2.Eval$0$result, inline$_v2.Eval$0$x := _v2.Eval_loop_anon3_LoopHead(inline$_v2.Eval$0$result, inline$_v2.Eval$0$x);
    _v2.Eval_loop_anon3_LoopHead_2_done := true;
    _v2.Eval_loop_anon3_LoopHead_out_2_0, _v2.Eval_loop_anon3_LoopHead_out_2_1, _v2.Eval_loop_anon3_LoopHead_out_2_2 := inline$_v2.Eval$0$result, inline$_v2.Eval$0$x, _v2.control_flag;
    goto inline$_v2.Eval$0$anon3_LoopHead_last;

  inline$_v2.Eval$0$anon3_LoopHead_last:
    goto inline$_v2.Eval$0$anon3_LoopDone, inline$_v2.Eval$0$anon3_LoopBody;

  inline$_v2.Eval$0$anon3_LoopBody:
    assume {:partition} inline$_v2.Eval$0$x > 0;
    _v2.control_flag := _v2.control_UIF(_v2.control_flag, 1);
    inline$_v2.Eval$0$result := inline$_v2.Eval$0$result + inline$_v2.Eval$0$x;
    havoc inline$_v2.Eval$0$result;
    inline$_v2.Eval$0$x := inline$_v2.Eval$0$x - 1;
    goto inline$_v2.Eval$0$anon3_LoopBody_dummy;

  inline$_v2.Eval$0$anon3_LoopBody_dummy:
    assume false;
    goto inline$_v2.Eval$0$Return;

  inline$_v2.Eval$0$anon3_LoopDone:
    assume {:partition} 0 >= inline$_v2.Eval$0$x;
    goto inline$_v2.Eval$0$anon2;

  inline$_v2.Eval$0$anon2:
    _v2.control_flag := _v2.control_UIF(_v2.control_flag, 2);
    goto inline$_v2.Eval$0$Return;

  inline$_v2.Eval$0$Return:
    assume true;
    assume true;
    assume true;
    assume true;
    _v2.result := inline$_v2.Eval$0$result;
    goto START$2;

  START$2:
    goto MS_L_0_0;

  MS_L_0_0:
    goto MS_L_taken_0, MS_L_not_taken_0;

  MS_L_taken_0:
    assume _v1.Eval_loop_anon3_LoopHead_1_done && _v2.Eval_loop_anon3_LoopHead_2_done;
    store__0__v1.control_flag := _v1.control_flag;
    store__0__v2.control_flag := _v2.control_flag;
    _v1.control_flag := _v1.Eval_loop_anon3_LoopHead_in_1_2;
    _v2.control_flag := _v2.Eval_loop_anon3_LoopHead_in_2_2;
    call out__v1.Eval_loop_anon3_LoopHead_out_1_0_0, out__v1.Eval_loop_anon3_LoopHead_out_1_1_0, out__v2.Eval_loop_anon3_LoopHead_out_2_0_0, out__v2.Eval_loop_anon3_LoopHead_out_2_1_0 := MS_Check__v1.Eval_loop_anon3_LoopHead___v2.Eval_loop_anon3_LoopHead(_v1.Eval_loop_anon3_LoopHead_in_1_0, _v1.Eval_loop_anon3_LoopHead_in_1_1, _v2.Eval_loop_anon3_LoopHead_in_2_0, _v2.Eval_loop_anon3_LoopHead_in_2_1);
    assume _v1.control_flag == _v1.Eval_loop_anon3_LoopHead_out_1_2;
    assume _v2.control_flag == _v2.Eval_loop_anon3_LoopHead_out_2_2;
    assume _v1.Eval_loop_anon3_LoopHead_out_1_0
     == out__v1.Eval_loop_anon3_LoopHead_out_1_0_0
   && _v1.Eval_loop_anon3_LoopHead_out_1_1
     == out__v1.Eval_loop_anon3_LoopHead_out_1_1_0
   && _v2.Eval_loop_anon3_LoopHead_out_2_0
     == out__v2.Eval_loop_anon3_LoopHead_out_2_0_0
   && _v2.Eval_loop_anon3_LoopHead_out_2_1
     == out__v2.Eval_loop_anon3_LoopHead_out_2_1_0;
    _v1.control_flag := store__0__v1.control_flag;
    _v2.control_flag := store__0__v2.control_flag;
    goto MS_L_meet_0;

  MS_L_not_taken_0:
    assume !(_v1.Eval_loop_anon3_LoopHead_1_done && _v2.Eval_loop_anon3_LoopHead_2_done);
    goto MS_L_meet_0;

  MS_L_meet_0:
    return;
}



function {:inline true} MS$_v1.Eval_loop_anon3_LoopHead$_v2.Eval_loop_anon3_LoopHead(_v1.in_result: int, 
    _v1.in_x: int, 
    _v1.control_flag_old: int, 
    _v1.control_flag_: int, 
    _v1.out_result: int, 
    _v1.out_x: int, 
    _v2.in_result: int, 
    _v2.in_x: int, 
    _v2.control_flag_old: int, 
    _v2.control_flag_: int, 
    _v2.out_result: int, 
    _v2.out_x: int)
   : bool
{
  true
}

const {:existential true} _houdini_Eval_loop_anon3_LoopHead_control_flag_2: bool;

const {:existential true} _houdini_Eval_loop_anon3_LoopHead_out_result_3: bool;

const {:existential true} _houdini_Eval_loop_anon3_LoopHead_out_x_4: bool;

procedure MS_Check__v1.Eval_loop_anon3_LoopHead___v2.Eval_loop_anon3_LoopHead(_v1.in_result: int, _v1.in_x: int, _v2.in_result: int, _v2.in_x: int)
   returns (_v1.out_result: int, _v1.out_x: int, _v2.out_result: int, _v2.out_x: int);
  modifies _v1.control_flag, _v2.control_flag;
  ensures MS$_v1.Eval_loop_anon3_LoopHead$_v2.Eval_loop_anon3_LoopHead(_v1.in_result, 
  _v1.in_x, 
  old(_v1.control_flag), 
  _v1.control_flag, 
  _v1.out_result, 
  _v1.out_x, 
  _v2.in_result, 
  _v2.in_x, 
  old(_v2.control_flag), 
  _v2.control_flag, 
  _v2.out_result, 
  _v2.out_x);
  ensures _houdini_Eval_loop_anon3_LoopHead_control_flag_2
   ==> 
  old(_v1.control_flag == _v2.control_flag && _v1.in_x == _v2.in_x)
   ==> _v1.control_flag == _v2.control_flag;
  ensures _houdini_Eval_loop_anon3_LoopHead_out_result_3
   ==> 
  old(_v1.in_result == _v2.in_result && _v1.in_x == _v2.in_x)
   ==> _v1.out_result == _v2.out_result;
  ensures _houdini_Eval_loop_anon3_LoopHead_out_x_4
   ==> 
  old(_v1.in_x == _v2.in_x)
   ==> _v1.out_x == _v2.out_x;



implementation MS_Check__v1.Eval_loop_anon3_LoopHead___v2.Eval_loop_anon3_LoopHead(_v1.in_result: int, _v1.in_x: int, _v2.in_result: int, _v2.in_x: int)
   returns (_v1.out_result: int, _v1.out_x: int, _v2.out_result: int, _v2.out_x: int)
{
  var inline$_v1.Eval_loop_anon3_LoopHead$0$in_result: int;
  var inline$_v1.Eval_loop_anon3_LoopHead$0$in_x: int;
  var inline$_v1.Eval_loop_anon3_LoopHead$0$out_result: int;
  var inline$_v1.Eval_loop_anon3_LoopHead$0$out_x: int;
  var inline$_v1.Eval_loop_anon3_LoopHead$0$_v1.control_flag: int;
  var inline$_v2.Eval_loop_anon3_LoopHead$0$in_result: int;
  var inline$_v2.Eval_loop_anon3_LoopHead$0$in_x: int;
  var inline$_v2.Eval_loop_anon3_LoopHead$0$out_result: int;
  var inline$_v2.Eval_loop_anon3_LoopHead$0$out_x: int;
  var inline$_v2.Eval_loop_anon3_LoopHead$0$_v2.control_flag: int;
  var _v1.Eval_loop_anon3_LoopHead_1_done: bool;
  var _v1.Eval_loop_anon3_LoopHead_in_1_0: int;
  var _v1.Eval_loop_anon3_LoopHead_in_1_1: int;
  var _v1.Eval_loop_anon3_LoopHead_in_1_2: int;
  var _v1.Eval_loop_anon3_LoopHead_out_1_0: int;
  var _v1.Eval_loop_anon3_LoopHead_out_1_1: int;
  var _v1.Eval_loop_anon3_LoopHead_out_1_2: int;
  var _v2.Eval_loop_anon3_LoopHead_2_done: bool;
  var _v2.Eval_loop_anon3_LoopHead_in_2_0: int;
  var _v2.Eval_loop_anon3_LoopHead_in_2_1: int;
  var _v2.Eval_loop_anon3_LoopHead_in_2_2: int;
  var _v2.Eval_loop_anon3_LoopHead_out_2_0: int;
  var _v2.Eval_loop_anon3_LoopHead_out_2_1: int;
  var _v2.Eval_loop_anon3_LoopHead_out_2_2: int;
  var store__0__v1.control_flag: int;
  var store__0__v2.control_flag: int;
  var out__v1.Eval_loop_anon3_LoopHead_out_1_0_0: int;
  var out__v1.Eval_loop_anon3_LoopHead_out_1_1_0: int;
  var out__v2.Eval_loop_anon3_LoopHead_out_2_0_0: int;
  var out__v2.Eval_loop_anon3_LoopHead_out_2_1_0: int;

  START:
    _v1.Eval_loop_anon3_LoopHead_1_done, _v2.Eval_loop_anon3_LoopHead_2_done := false, false;
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$Entry;

  inline$_v1.Eval_loop_anon3_LoopHead$0$Entry:
    inline$_v1.Eval_loop_anon3_LoopHead$0$in_result := _v1.in_result;
    inline$_v1.Eval_loop_anon3_LoopHead$0$in_x := _v1.in_x;
    havoc inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x;
    inline$_v1.Eval_loop_anon3_LoopHead$0$_v1.control_flag := _v1.control_flag;
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$entry;

  inline$_v1.Eval_loop_anon3_LoopHead$0$entry:
    inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x := inline$_v1.Eval_loop_anon3_LoopHead$0$in_result, inline$_v1.Eval_loop_anon3_LoopHead$0$in_x;
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopHead;

  inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopHead:
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopDone, inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopBody;

  inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopBody:
    assume {:partition} inline$_v1.Eval_loop_anon3_LoopHead$0$out_x > 0;
    _v1.control_flag := _v2.control_UIF(_v1.control_flag, 1);
    inline$_v1.Eval_loop_anon3_LoopHead$0$out_result := inline$_v1.Eval_loop_anon3_LoopHead$0$out_result
   + inline$_v1.Eval_loop_anon3_LoopHead$0$out_x;
    inline$_v1.Eval_loop_anon3_LoopHead$0$out_x := inline$_v1.Eval_loop_anon3_LoopHead$0$out_x - 1;
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopBody_dummy;

  inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopBody_dummy:
    _v1.Eval_loop_anon3_LoopHead_in_1_0, _v1.Eval_loop_anon3_LoopHead_in_1_1, _v1.Eval_loop_anon3_LoopHead_in_1_2 := inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x, _v1.control_flag;
    call inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x := _v1.Eval_loop_anon3_LoopHead(inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x);
    _v1.Eval_loop_anon3_LoopHead_1_done := true;
    _v1.Eval_loop_anon3_LoopHead_out_1_0, _v1.Eval_loop_anon3_LoopHead_out_1_1, _v1.Eval_loop_anon3_LoopHead_out_1_2 := inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x, _v1.control_flag;
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$Return;

  inline$_v1.Eval_loop_anon3_LoopHead$0$anon3_LoopDone:
    assume {:partition} 0 >= inline$_v1.Eval_loop_anon3_LoopHead$0$out_x;
    inline$_v1.Eval_loop_anon3_LoopHead$0$out_result, inline$_v1.Eval_loop_anon3_LoopHead$0$out_x := inline$_v1.Eval_loop_anon3_LoopHead$0$in_result, inline$_v1.Eval_loop_anon3_LoopHead$0$in_x;
    _v1.control_flag := inline$_v1.Eval_loop_anon3_LoopHead$0$_v1.control_flag;
    goto inline$_v1.Eval_loop_anon3_LoopHead$0$Return;

  inline$_v1.Eval_loop_anon3_LoopHead$0$Return:
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    _v1.out_result := inline$_v1.Eval_loop_anon3_LoopHead$0$out_result;
    _v1.out_x := inline$_v1.Eval_loop_anon3_LoopHead$0$out_x;
    goto START$1;

  START$1:
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$Entry;

  inline$_v2.Eval_loop_anon3_LoopHead$0$Entry:
    inline$_v2.Eval_loop_anon3_LoopHead$0$in_result := _v2.in_result;
    inline$_v2.Eval_loop_anon3_LoopHead$0$in_x := _v2.in_x;
    havoc inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x;
    inline$_v2.Eval_loop_anon3_LoopHead$0$_v2.control_flag := _v2.control_flag;
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$entry;

  inline$_v2.Eval_loop_anon3_LoopHead$0$entry:
    inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x := inline$_v2.Eval_loop_anon3_LoopHead$0$in_result, inline$_v2.Eval_loop_anon3_LoopHead$0$in_x;
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopHead;

  inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopHead:
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopDone, inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopBody;

  inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopBody:
    assume {:partition} inline$_v2.Eval_loop_anon3_LoopHead$0$out_x > 0;
    _v2.control_flag := _v2.control_UIF(_v2.control_flag, 1);
    inline$_v2.Eval_loop_anon3_LoopHead$0$out_result := inline$_v2.Eval_loop_anon3_LoopHead$0$out_result
   + inline$_v2.Eval_loop_anon3_LoopHead$0$out_x;
    havoc inline$_v2.Eval_loop_anon3_LoopHead$0$out_result;
    inline$_v2.Eval_loop_anon3_LoopHead$0$out_x := inline$_v2.Eval_loop_anon3_LoopHead$0$out_x - 1;
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopBody_dummy;

  inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopBody_dummy:
    _v2.Eval_loop_anon3_LoopHead_in_2_0, _v2.Eval_loop_anon3_LoopHead_in_2_1, _v2.Eval_loop_anon3_LoopHead_in_2_2 := inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x, _v2.control_flag;
    call inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x := _v2.Eval_loop_anon3_LoopHead(inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x);
    _v2.Eval_loop_anon3_LoopHead_2_done := true;
    _v2.Eval_loop_anon3_LoopHead_out_2_0, _v2.Eval_loop_anon3_LoopHead_out_2_1, _v2.Eval_loop_anon3_LoopHead_out_2_2 := inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x, _v2.control_flag;
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$Return;

  inline$_v2.Eval_loop_anon3_LoopHead$0$anon3_LoopDone:
    assume {:partition} 0 >= inline$_v2.Eval_loop_anon3_LoopHead$0$out_x;
    inline$_v2.Eval_loop_anon3_LoopHead$0$out_result, inline$_v2.Eval_loop_anon3_LoopHead$0$out_x := inline$_v2.Eval_loop_anon3_LoopHead$0$in_result, inline$_v2.Eval_loop_anon3_LoopHead$0$in_x;
    _v2.control_flag := inline$_v2.Eval_loop_anon3_LoopHead$0$_v2.control_flag;
    goto inline$_v2.Eval_loop_anon3_LoopHead$0$Return;

  inline$_v2.Eval_loop_anon3_LoopHead$0$Return:
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    _v2.out_result := inline$_v2.Eval_loop_anon3_LoopHead$0$out_result;
    _v2.out_x := inline$_v2.Eval_loop_anon3_LoopHead$0$out_x;
    goto START$2;

  START$2:
    goto MS_L_0_0;

  MS_L_0_0:
    goto MS_L_taken_0, MS_L_not_taken_0;

  MS_L_taken_0:
    assume _v1.Eval_loop_anon3_LoopHead_1_done && _v2.Eval_loop_anon3_LoopHead_2_done;
    store__0__v1.control_flag := _v1.control_flag;
    store__0__v2.control_flag := _v2.control_flag;
    _v1.control_flag := _v1.Eval_loop_anon3_LoopHead_in_1_2;
    _v2.control_flag := _v2.Eval_loop_anon3_LoopHead_in_2_2;
    call out__v1.Eval_loop_anon3_LoopHead_out_1_0_0, out__v1.Eval_loop_anon3_LoopHead_out_1_1_0, out__v2.Eval_loop_anon3_LoopHead_out_2_0_0, out__v2.Eval_loop_anon3_LoopHead_out_2_1_0 := MS_Check__v1.Eval_loop_anon3_LoopHead___v2.Eval_loop_anon3_LoopHead(_v1.Eval_loop_anon3_LoopHead_in_1_0, _v1.Eval_loop_anon3_LoopHead_in_1_1, _v2.Eval_loop_anon3_LoopHead_in_2_0, _v2.Eval_loop_anon3_LoopHead_in_2_1);
    assume _v1.control_flag == _v1.Eval_loop_anon3_LoopHead_out_1_2;
    assume _v2.control_flag == _v2.Eval_loop_anon3_LoopHead_out_2_2;
    assume _v1.Eval_loop_anon3_LoopHead_out_1_0
     == out__v1.Eval_loop_anon3_LoopHead_out_1_0_0
   && _v1.Eval_loop_anon3_LoopHead_out_1_1
     == out__v1.Eval_loop_anon3_LoopHead_out_1_1_0
   && _v2.Eval_loop_anon3_LoopHead_out_2_0
     == out__v2.Eval_loop_anon3_LoopHead_out_2_0_0
   && _v2.Eval_loop_anon3_LoopHead_out_2_1
     == out__v2.Eval_loop_anon3_LoopHead_out_2_1_0;
    _v1.control_flag := store__0__v1.control_flag;
    _v2.control_flag := store__0__v2.control_flag;
    goto MS_L_meet_0;

  MS_L_not_taken_0:
    assume !(_v1.Eval_loop_anon3_LoopHead_1_done && _v2.Eval_loop_anon3_LoopHead_2_done);
    goto MS_L_meet_0;

  MS_L_meet_0:
    return;
}


