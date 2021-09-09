// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure reqDef()
  free requires false;
  requires false;  // fails
  free requires {:alwaysAssume} false;
  requires false;
{
}

procedure testReq()
  ensures false;
{
  call reqDef();
}

procedure ensDef()
  free ensures false;
  ensures false;  // fails
  free ensures {:alwaysAssume} false;
  ensures false;
{
}
