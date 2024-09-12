// Boogie program verifier version 3.2.0.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: only-async-call-ISR.bpl /civlDesugaredFile:sugar.bpl /keepQuantifier

datatype main_f' {
  main_f'()
}

datatype main_f {
  main_f()
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_586(MapConst_603_586(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_606(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



procedure create_async_2389(PA: main_f);



procedure set_choice_2389(choice: main_f);



function {:builtin "MapConst"} MapConst_603_586(int) : [int]int;

function {:builtin "MapLe"} MapLe_586([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_606(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_606(a, MapNot_606(b))
}

function {:builtin "MapNot"} MapNot_606([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_606([int]bool, [int]bool) : [int]bool;

datatype Vec_603 {
  Vec_603(contents: [int]int, len: int)
}

function Default_603() : int;

function {:builtin "MapIte"} MapIte_627_603([int]bool, [int]int, [int]int) : [int]int;

function {:builtin "MapConst"} MapConst_5_586(bool) : [int]bool;

function Choice_586(a: [int]bool) : int;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_627_5([int]bool, [int]bool, [int]bool) : [int]bool;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_627_5(Range(0, x->len), MapConst_5_586(Default_5()), x->contents)
     == MapConst_5_586(Default_5()));

axiom (forall x: Vec_603 :: 
  { x->len } { x->contents } 
  MapIte_627_603(Range(0, x->len), MapConst_603_586(Default_603()), x->contents)
     == MapConst_603_586(Default_603()));

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall x: Vec_603 :: { x->len } x->len >= 0);

axiom (forall a: [int]bool :: 
  { Choice_586(a) } 
  a == MapConst_5_586(false) || a[Choice_586(a)]);

function {:builtin "MapAdd"} MapAdd_3611([main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapConst"} MapConst_3_3622(int) : [main_f']int;

function {:builtin "MapIte"} MapIte_3629_3([main_f']bool, [main_f']int, [main_f']int) : [main_f']int;

function {:builtin "MapAdd"} MapAdd_3643([main_f]int, [main_f]int) : [main_f]int;

function {:builtin "MapConst"} MapConst_3_3654(int) : [main_f]int;

function {:builtin "MapIte"} MapIte_3661_3([main_f]bool, [main_f]int, [main_f]int) : [main_f]int;

datatype Choice_Inv {
  Choice_Inv_main_f(main_f: main_f)
}

implementation main_f'()
{
  /*** structured program:
  **** end structured program */

  anon0:
    return;
}



procedure {:inline 1} main_f'();



function {:inline} Civl_InputOutputRelation_main_f'() : bool
{
  true
}

implementation Inv() returns (Civl_PAs_main_f: [main_f]int)
{
  /*** structured program:
    if (*)
    {
    }
    else
    {
        call create_async_2389(main_f());
        call set_choice_2389(main_f());
    }
  **** end structured program */

  anon0:
    Civl_PAs_main_f := MapConst_3_3654(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    Civl_PAs_main_f := MapAdd_3643(Civl_PAs_main_f, MapConst_3_3654(0)[main_f() := 1]);
    return;

  anon3_Then:
    return;
}



procedure {:inline 1} Inv() returns (Civl_PAs_main_f: [main_f]int);



function {:inline} Civl_InputOutputRelation_Inv(Civl_PAs_main_f: [main_f]int) : bool
{
  Civl_PAs_main_f == MapConst_3_3654(0)
     || Civl_PAs_main_f
       == MapAdd_3643(MapConst_3_3654(0), MapConst_3_3654(0)[main_f() := 1])
}

implementation Inv_With_Choice() returns (Civl_PAs_main_f: [main_f]int, Civl_choice: Choice_Inv)
{
  /*** structured program:
    if (*)
    {
    }
    else
    {
        call create_async_2389(main_f());
        call set_choice_2389(main_f());
    }
  **** end structured program */

  anon0:
    Civl_PAs_main_f := MapConst_3_3654(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    Civl_PAs_main_f := MapAdd_3643(Civl_PAs_main_f, MapConst_3_3654(0)[main_f() := 1]);
    assert Civl_PAs_main_f == MapConst_3_3654(0) || Civl_PAs_main_f[main_f()] > 0;
    Civl_choice->main_f := main_f();
    return;

  anon3_Then:
    return;
}



procedure {:inline 1} Inv_With_Choice() returns (Civl_PAs_main_f: [main_f]int, Civl_choice: Choice_Inv);



function {:inline} Civl_InputOutputRelation_Inv_With_Choice(Civl_PAs_main_f: [main_f]int, Civl_choice: Choice_Inv) : bool
{
  Civl_PAs_main_f == MapConst_3_3654(0)
     || (
      (Civl_PAs_main_f == MapConst_3_3654(0) || Civl_PAs_main_f[main_f()] > 0)
       && Civl_PAs_main_f
         == MapAdd_3643(MapConst_3_3654(0), MapConst_3_3654(0)[main_f() := 1])
       && Civl_choice == Choice_Inv_main_f(main_f()))
}

implementation Civl_Skip()
{

  init:
    return;
}



pure procedure {:inline 1} Civl_Skip();



function {:inline} Civl_InputOutputRelation_Civl_Skip() : bool
{
  true
}

implementation main_f() returns (Civl_PAs_main_f: [main_f]int)
{
  /*** structured program:
    if (*)
    {
    }
    else
    {
        call create_async_2389(main_f());
    }
  **** end structured program */

  anon0:
    Civl_PAs_main_f := MapConst_3_3654(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    Civl_PAs_main_f := MapAdd_3643(Civl_PAs_main_f, MapConst_3_3654(0)[main_f() := 1]);
    return;

  anon3_Then:
    return;
}



procedure {:inline 1} main_f() returns (Civl_PAs_main_f: [main_f]int);



function {:inline} Civl_InputOutputRelation_main_f(Civl_PAs_main_f: [main_f]int) : bool
{
  Civl_PAs_main_f == MapConst_3_3654(0)
     || Civl_PAs_main_f
       == MapAdd_3643(MapConst_3_3654(0), MapConst_3_3654(0)[main_f() := 1])
}

procedure Civl_proc_1();



implementation Civl_proc_1()
{
  /*** structured program:
    async call _main_f();
  **** end structured program */

  Civl_init:
    goto anon0;

  anon0:
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_1();
    assume false;
    return;

  Civl_RefinementChecker:
    assume false;
    return;

  Civl_UnchangedChecker:
    assume false;
    return;

  Civl_ReturnChecker:
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f_1() returns (Civl_PAs_main_f: [main_f]int);



implementation Civl_PendingAsyncNoninterferenceChecker_main_f_1() returns (Civl_PAs_main_f: [main_f]int)
{

  init:
    call Civl_PAs_main_f := main_f();
    call Civl_Wrapper_NoninterferenceChecker_1();
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1();



implementation Civl_Wrapper_NoninterferenceChecker_1()
{

  enter:
    return;
}



procedure Civl_proc_2();



implementation Civl_proc_2()
{
  var Civl_pc: bool;
  var Civl_ok: bool;
  var Civl_eval: bool;

  /*** structured program:
    async call _main_f();
  **** end structured program */

  Civl_init:
    Civl_pc, Civl_ok, Civl_eval := false, false, false;
    assume true;
    goto anon0;

  anon0:
    assert false;
    goto Civl_ReturnChecker, Civl_UnifiedReturn, Civl_NoninterferenceChecker;

  Civl_NoninterferenceChecker:
    call Civl_Wrapper_NoninterferenceChecker_2();
    assume false;
    return;

  Civl_RefinementChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_UnchangedChecker:
    assert true;
    assert Civl_pc ==> true;
    assume false;
    return;

  Civl_ReturnChecker:
    Civl_eval := true;
    assert true;
    assert Civl_pc ==> true;
    Civl_pc, Civl_ok := true ==> Civl_pc, Civl_eval || Civl_ok;
    assert Civl_ok;
    assume false;
    return;

  Civl_UnifiedReturn:
    return;
}



procedure Civl_PendingAsyncNoninterferenceChecker_main_f'_2();



implementation Civl_PendingAsyncNoninterferenceChecker_main_f'_2()
{

  init:
    call main_f'();
    call Civl_Wrapper_NoninterferenceChecker_2();
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_2();



implementation Civl_Wrapper_NoninterferenceChecker_2()
{

  enter:
    return;
}



procedure Civl_PartitionChecker_main_f() returns (Civl_PAs_main_f: [main_f]int);



implementation Civl_PartitionChecker_main_f() returns (Civl_PAs_main_f: [main_f]int)
{
  var Civl_local_Civl_PAs_main_f: main_f;

  Civl_PartitionChecker_main_f:
    call Civl_PAs_main_f := main_f();
    assert Civl_PAs_main_f != MapConst_3_3654(0) ==> true;
    goto label_Civl_PAs_main_f;

  label_Civl_PAs_main_f:
    assume Civl_PAs_main_f[Civl_local_Civl_PAs_main_f] >= 1;
    return;
}



procedure Civl_ISR_base_main_f() returns (Civl_PAs_main_f: [main_f]int);



implementation Civl_ISR_base_main_f() returns (Civl_PAs_main_f: [main_f]int)
{

  ISR_base_main_f:
    call Civl_PAs_main_f := main_f();
    assert Civl_PAs_main_f == MapConst_3_3654(0)
       || Civl_PAs_main_f
         == MapAdd_3643(MapConst_3_3654(0), MapConst_3_3654(0)[main_f() := 1]);
    return;
}



procedure Civl_ISR_conclusion_main_f() returns (Civl_PAs_main_f: [main_f]int);



implementation Civl_ISR_conclusion_main_f() returns (Civl_PAs_main_f: [main_f]int)
{

  ISR_conclusion_main_f:
    call Civl_PAs_main_f := Inv();
    assume Civl_PAs_main_f == MapConst_3_3654(0);
    assert true;
    return;
}



procedure Civl_ISR_step_Inv_main_f() returns (Civl_PAs_main_f: [main_f]int, Civl_choice: Choice_Inv);



implementation Civl_ISR_step_Inv_main_f() returns (Civl_PAs_main_f: [main_f]int, Civl_choice: Choice_Inv)
{
  var Civl_newPAs_main_f: [main_f]int;

  ISR_step_Inv_main_f:
    call Civl_PAs_main_f, Civl_choice := Inv_With_Choice();
    assume Civl_choice is Choice_Inv_main_f;
    assume Civl_PAs_main_f[Civl_choice->main_f] > 0;
    Civl_PAs_main_f[Civl_choice->main_f] := Civl_PAs_main_f[Civl_choice->main_f] - 1;
    call Civl_newPAs_main_f := main_f();
    Civl_PAs_main_f := MapAdd_3643(Civl_PAs_main_f, Civl_newPAs_main_f);
    assert Civl_PAs_main_f == MapConst_3_3654(0)
       || Civl_PAs_main_f
         == MapAdd_3643(MapConst_3_3654(0), MapConst_3_3654(0)[main_f() := 1]);
    return;
}



procedure Civl_ISR_AllPendingAsyncsInElim_main_f() returns (Civl_PAs_main_f: [main_f]int);



implementation Civl_ISR_AllPendingAsyncsInElim_main_f() returns (Civl_PAs_main_f: [main_f]int)
{

  ISR_AllPendingAsyncsInElim_main_f:
    assume true;
    call Civl_PAs_main_f := main_f();
    assert true;
    return;
}



procedure Civl_ISR_AllPendingAsyncsNotInElim_main_f() returns (Civl_PAs_main_f: [main_f]int);



implementation Civl_ISR_AllPendingAsyncsNotInElim_main_f() returns (Civl_PAs_main_f: [main_f]int)
{

  ISR_AllPendingAsyncsNotInElim_main_f:
    assume false;
    call Civl_PAs_main_f := main_f();
    assert Civl_PAs_main_f == MapConst_3_3654(0);
    return;
}



procedure Civl_ISR_InconsistencyChecker_main_f_main_f_main_f();



implementation Civl_ISR_InconsistencyChecker_main_f_main_f_main_f()
{
  var Civl_E1_main_f: main_f;
  var Civl_E2_main_f: main_f;

  ISR_InconsistencyChecker_main_f_main_f_main_f:
    assume true;
    assume true;
    assume true;
    assert !(true && false);
    return;
}


