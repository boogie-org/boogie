// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure reqDef0()
  free requires false;
  requires false;  // fails
  free requires {:always_assume} false; // this always_assumes comes too late to be useful to the previous line
{
}

procedure testReq0()
  ensures false;
{
  call reqDef0();
}

procedure reqDef1()
  free requires {:always_assume} false;
  requires false;
{
}

procedure testReq1()
  ensures false;
{
  call reqDef1();
}

procedure ensDef0()
  free ensures false;
  ensures false;  // fails
  free ensures {:always_assume} false; // this always_assumes comes too late to be useful to the previous line
{
}

procedure ensDef1()
  free ensures {:always_assume} false;
  ensures false;
{
}
