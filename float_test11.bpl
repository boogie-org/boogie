//Translation from interpolation.c
//Should Verify
//Returns inconclusive?  What does that mean?

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float32);
procedure main() returns () {
	var i : int;
	var z : float32;
	var t : float32;
	var min : [int] float32;
	var max : [int] float32;
	
	min[0] := TO_FLOAT32_INT(5);
	min[1] := TO_FLOAT32_INT(10);
	min[2] := TO_FLOAT32_INT(12);
	min[3] := TO_FLOAT32_INT(30);
	min[4] := TO_FLOAT32_INT(150);
	
	max[0] := TO_FLOAT32_INT(10);
	max[1] := TO_FLOAT32_INT(12);
	max[2] := TO_FLOAT32_INT(30);
	max[3] := TO_FLOAT32_INT(150);
	max[4] := TO_FLOAT32_INT(300);
	
	havoc t;
	assume(t >= min[0] && t <= max[4]);
	
	i := 0;
	//while (i < 5) {
		//if (t <= max[i]) {
			//break;
		//}
		//i := i + 1;
	//}
	
	if (t > max[0]) { //1
		i := i + 1;
	}
	if (t > max[1]) { //2
		i := i + 1;
	}
	if (t > max[2]) { //3
		i := i + 1;
	}
	if (t > max[3]) { //4
		i := i + 1;
	}
	if (t > max[4]) { //5
		i := i + 1;
	}
	
	z := (t - min[i]) / (max[i] - min[i]);
	
	assert(z >= TO_FLOAT32_INT(0) && z <= TO_FLOAT32_INT(1));
}