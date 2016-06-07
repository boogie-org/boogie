// RUN: %boogie -noinfer -useArrayTheory "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var k: int;
var AllMaps__1: [int][int]int;

procedure PoirotMain.Main_trace_1_trace_1()
modifies k, AllMaps__1;
{
  var $tmp4: int;
  var local_0: int;

  lab0:
    k := 1;
    goto lab1, lab2;


lab1:
    assume k == 0;
    goto lab3;

lab2:
    assume k == 1;
    $tmp4 := local_0;
    goto lab3;

lab3:    
    AllMaps__1[$tmp4][0] := 1;   
    assert AllMaps__1[local_0][0] == 1;
}


