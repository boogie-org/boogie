// RUN: %boogie -noVerify -print:- -env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
function \true() returns(bool);

type \procedure;
procedure \old(\any : \procedure) returns(\var : \procedure)
{
  var \modifies : \procedure;
  \modifies := \any;
  \var := \modifies;
}

procedure qux(a : \procedure)
{
  var \var : \procedure; var x : bool;
  call \var := \old(a);
  x := \true();
}
