procedure F() returns () {
	Logic=QF_FP;
	var x : float;
	x := fp(.1) + fp(.1);
	assert x == fp(.2);
}