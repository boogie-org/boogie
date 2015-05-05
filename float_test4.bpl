 procedure F() returns () {
	var x : float;
	var y : float;
	y := x - x;
	assert y == fp (0,0,23,8);
}