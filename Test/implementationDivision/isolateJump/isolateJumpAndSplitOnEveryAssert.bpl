// RUN: %boogie /printSplit:- /errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure {:vcs_split_on_every_assert} MergeAtEnd(x: int) returns (r: int) 
  ensures r > 1;
{
  if (x > 0) {
    r := 1;
  } 
  else {
    r := 2;
  }
}

procedure {:vcs_split_on_every_assert} MultipleEnsures(x: int) returns (r: int) 
  ensures r > 1;
  ensures r < 10;
{
  if (x > 0) {
    r := 1;
    return;
  } 
  else {
    r := 20;
    return;
  }
}