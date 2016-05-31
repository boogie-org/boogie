//Translation from drift_tenth.c
//Should Fail

function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_INT(int) returns (float32);
function {:builtin "(_ to_fp 8 24) RNE"} TO_FLOAT32_REAL(real) returns (float32);

procedure main() returns () {
	var tick : float32;
	var time : float32;
	var i: int;
	
	tick := TO_FLOAT32_INT(1)/TO_FLOAT32_INT(10);
	time := TO_FLOAT32_INT(0);
	
	//i := 0;
	//while (i < 10)
	//{
	//	time := time + tick;
	//	i := i + 1;
	//}
	time := time + tick;//1
	time := time + tick;//2
	time := time + tick;//3
	time := time + tick;//4
	time := time + tick;//5
	time := time + tick;//6
	time := time + tick;//7
	time := time + tick;//8
	time := time + tick;//9
	time := time + tick;//10
	assert time == TO_FLOAT32_INT(1);
}