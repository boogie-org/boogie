//Translation from drift_tenth.c
//Should Verify
//FAILS; note that it succeeds when tick == fp(.1)

procedure main() returns () {
	var tick : float;
	var time : float;
	var i: int;
	
	tick := fp(1)/fp(10);
	time := fp(0);
	
	i := 0;
	while (i < 10)
	{
		time := time + tick;
		i := i + 1;
	}
	assert(time == fp(1));
}