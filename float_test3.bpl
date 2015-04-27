 procedure F() returns () {
	var x : float;
	var y : float;
	y := x - x;
	assert y != x;
}