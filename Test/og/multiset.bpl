type X;

const unique null : int;
const nil: X;

var {:qed} elt : [int]int;
var {:qed} valid : [int]bool;
var {:qed} lock : [int]X;
const max : int;

axiom (max > 0);

procedure {:yields} acquire(i : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:right 0} |{ A: 
                      assert 0 <= i && i < max;
                      assert tidIn != nil;
                      assume lock[i] == nil;
                      tidOut := tidIn;
	              lock[i] := tidOut;
                      return true;
                    }|;


procedure {:yields} release(i : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:left 0} |{ A: 
                     assert 0 <= i && i < max;
                     assert lock[i] == tidIn;
                     assert tidIn != nil; 
                     tidOut := tidIn;
	             lock[i] := nil;
                     return true;
                    }|;


procedure {:yields} getElt(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X, elt_j:int);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil;
                     tidOut := tidIn;
	             elt_j := elt[j];
                     return true;
                    }|;


procedure {:yields} setElt(j : int, x : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil;
                     tidOut := tidIn;
	             elt[j] := x;
                     return true;
                    }|;

procedure {:yields} getValid(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X, valid_j:bool);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil;
                     tidOut := tidIn;
	             valid_j := valid[j];
                     return true;
                    }|;


procedure {:yields} setValid(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil;
                     tidOut := tidIn;
	             valid[j] := true;
                     return true;
                    }|;


procedure {:yields} FindSlot(x : int, {:linear "tid"} tidIn: X) returns (r : int, {:linear "tid"} tidOut: X)
ensures {:right 1}  |{ A: assert tidIn != nil; 
                          assert x != null; 
                          havoc r; assume (-1 <= r && r < max); goto B, C;
                       B: assume (r != -1); 
                                            assume elt[r] == null; 
                                            elt[r] := x; 
                                            tidOut := tidIn; 
                                            return true;
                       C: assume (r == -1); tidOut := tidIn; return true; 
                   }|;
{
	var j : int;
	var elt_j : int;
        var {:linear "tid"} tidTmp: X;
        
        yield;
	j := 0;
        tidTmp := tidIn;

	
	while(j < max)
        invariant {:phase 1} tidTmp != nil;
        invariant {:phase 1} tidTmp == tidIn;
	{
                yield;
                call tidTmp := acquire(j, tidTmp);
                call tidTmp, elt_j := getElt(j, tidTmp);
		if(elt_j == null)
		{
                        call tidTmp := setElt(j, x, tidTmp);
			call tidTmp := release(j, tidTmp);
			r := j;
                        tidOut := tidTmp;
                        yield;
			return;		
		}
		call tidTmp := release(j,tidTmp);
                yield;
		j := j + 1;	
	}
	r := -1;
        tidOut := tidTmp;
	return;
}

// procedure {:yields} Foo({:linear "tid"} tidIn: X) {
//      var i:int;
//      var x:int;
//      var {:linear "tid"} tidTmp: X;

//      tidTmp := tidIn;
//            yield;
//            havoc x;
//            assume x != null;
//            call i, tidTmp := FindSlot(x, tidTmp);      
//            yield;
// }



procedure {:yields} Insert(x : int, {:linear "tid"} tidIn: X) returns (result : bool, i : int, {:linear "tid"} tidOut: X) 
requires {:phase 2} Inv(valid, elt);
ensures {:phase 2} Inv(valid, elt);
ensures {:atomic 2}  |{ var r:int;
                        A: assert tidIn != nil; 
                           assert x != null;
                           havoc r; assume (-1 <= r && r < max); goto B, C;
                        B: assume (r != -1); 
                           assume valid[r] == false; 
                           assume elt[r] == null; 
                           elt[r] := x; valid[r] := true; tidOut := tidIn; result := true; return true;
                        C: tidOut := tidIn; result := false; return true; 
                      }|;
 {

        var {:linear "tid"} tidTmp: X;
        tidTmp := tidIn;

        yield;
        assert {:phase 2} Inv(valid, elt);
        call i, tidTmp := FindSlot(x, tidTmp);
        
	if(i == -1)
	{
		result := false;
                tidOut := tidTmp;
	        yield;
                assert {:phase 2} Inv(valid, elt);
		return;
	}
        par Yield1();
        assert {:phase 2} i != -1;
	call tidTmp := acquire(i, tidTmp);
        assert {:phase 2} elt[i] == x;
	assert {:phase 2}  valid[i] == false;
        call tidTmp := setValid(i, tidTmp);   
	call tidTmp := release(i, tidTmp);
	result := true; 
        tidOut := tidTmp;
        yield;
        assert {:phase 2} Inv(valid, elt);
	return;
}

procedure {:yields} {:stable} Yield1()
ensures {:both 1} |{ A: return true; }|;
{
}

function {:inline} Inv(valid: [int]bool, elt: [int]int): (bool)
{
   ( forall i:int :: 0 <= i && i < max ==> (elt[i] == null <==> !valid[i]) )
}
