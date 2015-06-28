// RUN: %boogie -typeEncoding:m "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type{:datatype} finite_map;
function{:constructor} finite_map(dom:[int]bool, map:[int]int):finite_map;

type{:datatype} partition;
function{:constructor} partition(owners:[int]int, vars:[int]finite_map):partition;

procedure P(arr:finite_map)
  requires dom#finite_map(arr)[0];
  ensures  dom#finite_map(arr)[0];
{
}
