type X;

const unique null : int;
const unique nil: X;
const unique done: X;

var {:qed} elt : [int]int;
var {:qed} valid : [int]bool;
var {:qed} lock : [int]X;
var {:qed} owner : [int]X;
const max : int;

axiom (max > 0);

procedure {:yields} acquire(i : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:right 0} |{ A: 
                      assert 0 <= i && i < max;
                      assert tidIn != nil && tidIn != done;
                      assume lock[i] == nil;
                      tidOut := tidIn;
	              lock[i] := tidOut;
                      return true;
                    }|;


procedure {:yields} release(i : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:left 0} |{ A: 
                     assert 0 <= i && i < max;
                     assert lock[i] == tidIn;
                     assert tidIn != nil && tidIn != done; 
                     tidOut := tidIn;
	             lock[i] := nil;
                     return true;
                    }|;


procedure {:yields} getElt(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X, elt_j:int);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil && tidIn != done;
                     tidOut := tidIn;
	             elt_j := elt[j];
                     return true;
                    }|;


procedure {:yields} setElt(j : int, x : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:both 0} |{ A: 
                     assert x != null;
                     assert owner[j] == nil;
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil && tidIn != done;
                     tidOut := tidIn;
	             elt[j] := x;
                     owner[j] := tidIn;
                     return true;
                    }|;


procedure {:yields} setEltToNull(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:left 0} |{ A: 
                     assert owner[j] == tidIn;
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert !valid[j];
                     assert tidIn != nil  && tidIn != done;
                     tidOut := tidIn;
	             elt[j] := null;
                     owner[j] := nil;
                     return true;
                    }|;




procedure {:yields} getValid(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X, valid_j:bool);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil  && tidIn != done;
                     tidOut := tidIn;
	             valid_j := valid[j];
                     return true;
                    }|;


procedure {:yields} setValid(j : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X);
ensures {:both 0} |{ A: 
                     assert 0 <= j && j < max;
                     assert lock[j] == tidIn;
                     assert tidIn != nil && tidIn != done;
                     assert owner[j] == tidIn;
                     tidOut := tidIn;
	             valid[j] := true;
                     owner[j] := done;
                     return true;
                    }|;

procedure {:yields} isEltThereAndValid(j : int, x : int, {:linear "tid"} tidIn: X) returns ({:linear "tid"} tidOut: X, fnd:bool);
ensures {:both 0} |{ A: 
                       assert 0 <= j && j < max;
                       assert lock[j] == tidIn;
                       assert tidIn != nil && tidIn != done;
                       tidOut := tidIn;
                       fnd := (elt[j] == x) && valid[j];
                       return true;
                    }|;

procedure {:yields} FindSlot(x : int, {:linear "tid"} tidIn: X) returns (r : int, {:linear "tid"} tidOut: X)
requires {:phase 1} Inv(valid, elt, owner);
ensures {:phase 1} Inv(valid, elt, owner);
ensures {:right 1}  |{ A: assert tidIn != nil && tidIn != done; 
                          assert x != null; 
                          havoc r; assume (-1 <= r && r < max); goto B, C;
                       B: assume (r != -1); 
                                            assume elt[r] == null; 
                                            assume owner[r] == nil;
					    assume !valid[r];
                                            elt[r] := x; 
                                            owner[r] := tidIn;
                                            tidOut := tidIn; 
                                            return true;
                       C: assume (r == -1); tidOut := tidIn; return true; 
                   }|;
{
	var j : int;
	var elt_j : int;
        var {:linear "tid"} tidTmp: X;
        
        par Yield1();

	j := 0;
        tidTmp := tidIn;

	
	while(j < max)
        invariant {:phase 1} tidTmp != nil && tidTmp != done;
        invariant {:phase 1} tidTmp == tidIn;
        invariant {:phase 1} Inv(valid, elt, owner);
	{
                par Yield1();

                call tidTmp := acquire(j, tidTmp);
                call tidTmp, elt_j := getElt(j, tidTmp);
		if(elt_j == null)
		{
                        call tidTmp := setElt(j, x, tidTmp);
			call tidTmp := release(j, tidTmp);
			r := j;
                        tidOut := tidTmp;

                        par Yield1();

			return;		
		}
		call tidTmp := release(j,tidTmp);

                par Yield1();

		j := j + 1;	
	}
	r := -1;
        tidOut := tidTmp;
	return;
}

procedure {:yields} Insert(x : int, {:linear "tid"} tidIn: X) returns (result : bool, i : int, {:linear "tid"} tidOut: X) 
requires {:phase 1} Inv(valid, elt, owner);
requires {:phase 2} Inv(valid, elt, owner);
ensures {:phase 1} Inv(valid, elt, owner);
requires {:phase 2} Inv(valid, elt, owner);
ensures {:atomic 2}  |{ var r:int;
                        A: assert tidIn != nil && tidIn != done; 
                           assert x != null;
                           havoc r; assume (-1 <= r && r < max); goto B, C;
                        B: assume (r != -1); 
                           assume valid[r] == false; 
                           assume elt[r] == null; 
                           assume owner[r] == nil; 
                           elt[r] := x; valid[r] := true; owner[r] := done;
                           tidOut := tidIn; result := true; return true;
                        C: tidOut := tidIn; result := false; return true; 
                      }|;
 {

        var {:linear "tid"} tidTmp: X;
        par Yield12();
        tidTmp := tidIn;
        call i, tidTmp := FindSlot(x, tidTmp);
        
	if(i == -1)
	{
		result := false;
                tidOut := tidTmp;
                par Yield12();
		return;
	}
        par Yield1();
        assert {:phase 1} i != -1;
        assert {:phase 2} i != -1;
	call tidTmp := acquire(i, tidTmp);
        assert {:phase 2} elt[i] == x;
	assert {:phase 2}  valid[i] == false;
        call tidTmp := setValid(i, tidTmp);   
	call tidTmp := release(i, tidTmp);
	result := true; 
        tidOut := tidTmp;
        par Yield12();
	return;
}

procedure {:yields} InsertPair(x : int, 
                               y : int, 
                               {:linear "tid"} tidIn: X) 
                               returns (result : bool, 
                                        i : int, 
                                        j : int,
                                        {:linear "tid"} tidOut: X) 
requires {:phase 1} Inv(valid, elt, owner);
ensures {:phase 1} Inv(valid, elt, owner);
requires {:phase 2} Inv(valid, elt, owner);
ensures {:phase 2} Inv(valid, elt, owner);
ensures {:atomic 2}  |{ var rx:int;
                        var ry:int;
                        A: assert tidIn != nil && tidIn != done; 
                           assert x != null && y != null;
                           havoc rx; assume (-1 <= rx && rx < max); 
                           havoc ry; assume (-1 <= ry && ry < max);
                           assume (rx == ry ==> rx == -1);
                           goto B, C;
                        B: assume (rx != -1 && ry != -1); 
                           assume valid[rx] == false; 
                           assume valid[ry] == false; 
                           assume elt[rx] == null; 
                           assume elt[rx] == null; 
                           elt[rx] := x; 
                           elt[ry] := y; 
                           valid[rx] := true; 
                           valid[ry] := true;
                           owner[rx] := done;
                           owner[ry] := done; 
                           tidOut := tidIn; 
                           result := true; return true;
                        C: tidOut := tidIn; 
                           result := false; return true; 
                      }|;
 {

        var {:linear "tid"} tidTmp: X;
        par Yield12();

        tidTmp := tidIn;

        call i, tidTmp := FindSlot(x, tidTmp);
        
	if (i == -1)
	{
	 	result := false;
                tidOut := tidTmp;
                par Yield12();
		return;
	}

        par Yield1();
        call j, tidTmp := FindSlot(y, tidTmp);
        
	if(j == -1)
	{
                par Yield1();
                call tidTmp := acquire(i,tidTmp);  
                call tidTmp := setEltToNull(i, tidTmp);
                call tidTmp := release(i,tidTmp);  
		result := false;
                tidOut := tidTmp;
                par Yield12();
		return;
	}

        par Yield1();
        assert {:phase 2} i != -1 && j != -1;
	call tidTmp := acquire(i, tidTmp);
	call tidTmp := acquire(j, tidTmp);
        assert {:phase 2} elt[i] == x;
        assert {:phase 2} elt[j] == y;
	assert {:phase 2}  valid[i] == false;
	assert {:phase 2}  valid[j] == false;
        call tidTmp := setValid(i, tidTmp);   
        call tidTmp := setValid(j, tidTmp);   
	call tidTmp := release(j, tidTmp);
	call tidTmp := release(i, tidTmp);
	result := true; 
        tidOut := tidTmp;
        par Yield12();
	return;
}

procedure {:yields} LookUp(x : int, {:linear "tid"} tidIn: X, old_valid:[int]bool, old_elt:[int]int) returns (found : bool, {:linear "tid"} tidOut: X)
requires {:phase 1} {:phase 2} old_valid == valid && old_elt == elt;
requires {:phase 1} {:phase 2} Inv(valid, elt, owner);
requires {:phase 1} {:phase 2} (tidIn != nil && tidIn != done);
ensures {:phase 1} {:phase 2} Inv(valid, elt, owner);
ensures {:atomic 2}  |{ A: assert tidIn != nil && tidIn != done; 
                          assert x != null;
			  havoc found; 
                          assume found ==> (exists ii:int :: 0 <= ii && ii < max && valid[ii] && elt[ii] == x);
                          return true;
                    }|;
ensures {:phase 2} !found ==> (forall ii:int :: 0 <= ii && ii < max ==> !(old_valid[ii] && old_elt[ii] == x));
{
	var j : int;
	var isThere : bool;
        var {:linear "tid"} tidTmp: X;
        
        par Yield12() | YieldLookUp(old_valid, old_elt);

	j := 0;
        tidTmp := tidIn;

	while(j < max)
        invariant {:phase 1} {:phase 2} tidTmp != nil && tidTmp != done;
        invariant {:phase 1} {:phase 2} tidTmp == tidIn;
        invariant {:phase 1} {:phase 2} Inv(valid, elt, owner);
        invariant {:phase 1} {:phase 2} (forall ii:int :: 0 <= ii && ii < j ==> !(old_valid[ii] && old_elt[ii] == x));
	invariant {:phase 1} {:phase 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
	{
                par Yield12() | YieldLookUp(old_valid, old_elt);

                call tidTmp := acquire(j, tidTmp);
                call tidTmp, isThere := isEltThereAndValid(j, x, tidTmp);
		if(isThere)
		{
			 call tidTmp := release(j, tidTmp);
                         found := true; 
                         tidOut := tidTmp;
                         par Yield12() | YieldLookUp(old_valid, old_elt);
		 	 return;		
		}
		call tidTmp := release(j,tidTmp);
                par Yield12() | YieldLookUp(old_valid, old_elt);
		j := j + 1;	
	}
	found := false;
        tidOut := tidTmp;
	return;
}

procedure {:yields} {:stable} Yield1()
requires {:phase 1} Inv(valid, elt, owner);
ensures {:phase 1} Inv(valid, elt, owner);
ensures {:both 1} |{ A: return true; }|;
{
}

procedure {:yields} {:stable} Yield12()
requires {:phase 1} {:phase 2} Inv(valid, elt, owner);
ensures {:phase 1} {:phase 2} Inv(valid, elt, owner);
{
        yield;
        assert {:phase 1} {:phase 2} Inv(valid, elt, owner);
}

function {:inline} Inv(valid: [int]bool, elt: [int]int, owner: [int]X): (bool)
{
   (forall i:int :: 0 <= i && i < max ==> (elt[i] == null <==> (!valid[i] && owner[i] == nil)))
}

procedure {:yields} {:stable} YieldLookUp(old_valid: [int]bool, old_elt: [int]int)
requires {:phase 1} {:phase 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
ensures {:phase 1} {:phase 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
{
    yield;
    assert {:phase 1} {:phase 2} (forall ii:int :: 0 <= ii && ii < max && old_valid[ii] ==> valid[ii] && old_elt[ii] == elt[ii]);
}
