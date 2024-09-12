// Boogie program verifier version 3.1.6.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options: is2-attributes.bpl /civlDesugaredFile:namratha.bpl

datatype main_f'' {
  main_f''()
}

const Identity: [int]int;

function {:inline} AtLeast(x: int) : [int]bool
{
  MapLe_567(MapConst_584_567(x), Identity)
}

function {:inline} Range(from: int, n: int) : [int]bool
{
  MapDiff_587(AtLeast(from), AtLeast(from + n))
}

type {:builtin "Seq"} Seq _;

pure procedure Assume(b: bool);
  ensures b;



procedure create_async_2608(PA: main_f'');



procedure set_choice_2608(choice: main_f'');



function {:builtin "MapConst"} MapConst_584_567(int) : [int]int;

function {:builtin "MapLe"} MapLe_567([int]int, [int]int) : [int]bool;

function {:inline} MapDiff_587(a: [int]bool, b: [int]bool) : [int]bool
{
  MapAnd_587(a, MapNot_587(b))
}

function {:builtin "MapNot"} MapNot_587([int]bool) : [int]bool;

function {:builtin "MapAnd"} MapAnd_587([int]bool, [int]bool) : [int]bool;

datatype Vec_584 {
  Vec_584(contents: [int]int, len: int)
}

function Default_584() : int;

function {:builtin "MapIte"} MapIte_608_584([int]bool, [int]int, [int]int) : [int]int;

function {:builtin "MapConst"} MapConst_5_567(bool) : [int]bool;

function Choice_567(a: [int]bool) : int;

datatype Vec_5 {
  Vec_5(contents: [int]bool, len: int)
}

function Default_5() : bool;

function {:builtin "MapIte"} MapIte_608_5([int]bool, [int]bool, [int]bool) : [int]bool;

axiom (forall x: int :: Identity[x] == x);

axiom (forall x: Vec_5 :: 
  { x->len } { x->contents } 
  MapIte_608_5(Range(0, x->len), MapConst_5_567(Default_5()), x->contents)
     == MapConst_5_567(Default_5()));

axiom (forall x: Vec_584 :: 
  { x->len } { x->contents } 
  MapIte_608_584(Range(0, x->len), MapConst_584_567(Default_584()), x->contents)
     == MapConst_584_567(Default_584()));

axiom (forall x: Vec_5 :: { x->len } x->len >= 0);

axiom (forall x: Vec_584 :: { x->len } x->len >= 0);

axiom true;

axiom true;

axiom true;

axiom true;

axiom true;

axiom true;

axiom (forall a: [int]bool :: 
  { Choice_567(a) } 
  a == MapConst_5_567(false) || a[Choice_567(a)]);

function {:builtin "MapAdd"} MapAdd_4231([main_f'']int, [main_f'']int) : [main_f'']int;

function {:builtin "MapConst"} MapConst_3_4242(int) : [main_f'']int;

function {:builtin "MapIte"} MapIte_4249_3([main_f'']bool, [main_f'']int, [main_f'']int) : [main_f'']int;

datatype Choice_Inv {
  Choice_Inv_main_f''(main_f'': main_f'')
}

implementation final()
{
  /*** structured program:
  **** end structured program */

  anon0:
    return;
}



procedure {:inline 1} final();



function {:inline} Civl_InputOutputRelation_final() : bool
{
  true
}

implementation Inv() returns (Civl_PAs_main_f'': [main_f'']int)
{
  /*** structured program:
    if (*)
    {
    }
    else
    {
        call create_async_2608(main_f''());
        call set_choice_2608(main_f''());
    }
  **** end structured program */

  anon0:
    Civl_PAs_main_f'' := MapConst_3_4242(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    Civl_PAs_main_f'' := MapAdd_4231(Civl_PAs_main_f'', MapConst_3_4242(0)[main_f''() := 1]);
    return;

  anon3_Then:
    return;
}



procedure {:inline 1} Inv() returns (Civl_PAs_main_f'': [main_f'']int);



function {:inline} Civl_InputOutputRelation_Inv(Civl_PAs_main_f'': [main_f'']int) : bool
{
  Civl_PAs_main_f'' == MapConst_3_4242(0)
     || Civl_PAs_main_f''
       == MapAdd_4231(MapConst_3_4242(0), MapConst_3_4242(0)[main_f''() := 1])
}

implementation Inv_With_Choice() returns (Civl_PAs_main_f'': [main_f'']int, Civl_choice: Choice_Inv)
{
  /*** structured program:
    if (*)
    {
    }
    else
    {
        call create_async_2608(main_f''());
        call set_choice_2608(main_f''());
    }
  **** end structured program */

  anon0:
    Civl_PAs_main_f'' := MapConst_3_4242(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    Civl_PAs_main_f'' := MapAdd_4231(Civl_PAs_main_f'', MapConst_3_4242(0)[main_f''() := 1]);
    assert Civl_PAs_main_f'' == MapConst_3_4242(0) || Civl_PAs_main_f''[main_f''()] > 0;
    Civl_choice->main_f'' := main_f''();
    return;

  anon3_Then:
    return;
}



procedure {:inline 1} Inv_With_Choice() returns (Civl_PAs_main_f'': [main_f'']int, Civl_choice: Choice_Inv);



function {:inline} Civl_InputOutputRelation_Inv_With_Choice(Civl_PAs_main_f'': [main_f'']int, Civl_choice: Choice_Inv) : bool
{
  Civl_PAs_main_f'' == MapConst_3_4242(0)
     || (
      (Civl_PAs_main_f'' == MapConst_3_4242(0) || Civl_PAs_main_f''[main_f''()] > 0)
       && Civl_PAs_main_f''
         == MapAdd_4231(MapConst_3_4242(0), MapConst_3_4242(0)[main_f''() := 1])
       && Civl_choice == Choice_Inv_main_f''(main_f''()))
}

implementation main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{
  /*** structured program:
    if (*)
    {
    }
    else
    {
        call create_async_2608(main_f''());
    }
  **** end structured program */

  anon0:
    Civl_PAs_main_f'' := MapConst_3_4242(0);
    goto anon3_Then, anon3_Else;

  anon3_Else:
    Civl_PAs_main_f'' := MapAdd_4231(Civl_PAs_main_f'', MapConst_3_4242(0)[main_f''() := 1]);
    return;

  anon3_Then:
    return;
}



procedure {:inline 1} main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



function {:inline} Civl_InputOutputRelation_main_f''(Civl_PAs_main_f'': [main_f'']int) : bool
{
  Civl_PAs_main_f'' == MapConst_3_4242(0)
     || Civl_PAs_main_f''
       == MapAdd_4231(MapConst_3_4242(0), MapConst_3_4242(0)[main_f''() := 1])
}

procedure Civl_PendingAsyncNoninterferenceChecker_main_f''_1() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_PendingAsyncNoninterferenceChecker_main_f''_1() returns (Civl_PAs_main_f'': [main_f'']int)
{

  init:
    call Civl_PAs_main_f'' := main_f''();
    call Civl_Wrapper_NoninterferenceChecker_1();
    return;
}



procedure {:inline 1} Civl_Wrapper_NoninterferenceChecker_1();



implementation Civl_Wrapper_NoninterferenceChecker_1()
{

  enter:
    return;
}



procedure Civl_PartitionChecker_main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_PartitionChecker_main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{
  var Civl_local_Civl_PAs_main_f'': main_f'';

  Civl_PartitionChecker_main_f'':
    call Civl_PAs_main_f'' := main_f''();
    assert Civl_PAs_main_f'' != MapConst_3_4242(0) ==> true;
    goto label_Civl_PAs_main_f'';

  label_Civl_PAs_main_f'':
    assume Civl_PAs_main_f''[Civl_local_Civl_PAs_main_f''] >= 1;
    return;
}



procedure Civl_ISR_base_main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_ISR_base_main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{

  ISR_base_main_f'':
    call Civl_PAs_main_f'' := main_f''();
    assert Civl_PAs_main_f'' == MapConst_3_4242(0)
       || Civl_PAs_main_f''
         == MapAdd_4231(MapConst_3_4242(0), MapConst_3_4242(0)[main_f''() := 1]);
    return;
}



procedure Civl_ISR_conclusion_main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_ISR_conclusion_main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{

  ISR_conclusion_main_f'':
    call Civl_PAs_main_f'' := Inv();
    assume Civl_PAs_main_f'' == MapConst_3_4242(0);
    assert true;
    return;
}



procedure Civl_ISR_step_Inv_main_f''() returns (Civl_PAs_main_f'': [main_f'']int, Civl_choice: Choice_Inv);



implementation Civl_ISR_step_Inv_main_f''() returns (Civl_PAs_main_f'': [main_f'']int, Civl_choice: Choice_Inv)
{
  var Civl_newPAs_main_f'': [main_f'']int;

  ISR_step_Inv_main_f'':
    call Civl_PAs_main_f'', Civl_choice := Inv_With_Choice();
    assume Civl_choice is Choice_Inv_main_f'';
    assume Civl_PAs_main_f''[Civl_choice->main_f''] > 0;
    Civl_PAs_main_f''[Civl_choice->main_f''] := Civl_PAs_main_f''[Civl_choice->main_f''] - 1;
    call Civl_newPAs_main_f'' := main_f''();
    Civl_PAs_main_f'' := MapAdd_4231(Civl_PAs_main_f'', Civl_newPAs_main_f'');
    assert Civl_PAs_main_f'' == MapConst_3_4242(0)
       || Civl_PAs_main_f''
         == MapAdd_4231(MapConst_3_4242(0), MapConst_3_4242(0)[main_f''() := 1]);
    return;
}



procedure Civl_ISR_SideCondition_main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_ISR_SideCondition_main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{

  init:
    call Civl_PAs_main_f'' := main_f''();
    return;
}



procedure Civl_ISR_ExitProperty1Checker_main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_ISR_ExitProperty1Checker_main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{

  ISR_ExitProperty1Checker_main_f'':
    assume false;
    call Civl_PAs_main_f'' := main_f''();
    assert Civl_PAs_main_f'' == MapConst_3_4242(0);
    return;
}



procedure Civl_ISR_ExitProperty2Checker_main_f''() returns (Civl_PAs_main_f'': [main_f'']int);



implementation Civl_ISR_ExitProperty2Checker_main_f''() returns (Civl_PAs_main_f'': [main_f'']int)
{

  ISR_ExitProperty2Checker_main_f'':
    assume true;
    call Civl_PAs_main_f'' := main_f''();
    assert true;
    return;
}



procedure Civl_ISR_InconsistencyChecker_main_f''_main_f''_main_f''();



implementation Civl_ISR_InconsistencyChecker_main_f''_main_f''_main_f''()
{
  var Civl_E1_main_f'': main_f'';
  var Civl_E2_main_f'': main_f'';

  ISR_InconsistencyChecker_main_f''_main_f''_main_f'':
    assume true;
    assume true;
    assume true;
    assert !(true && false);
    return;
}


