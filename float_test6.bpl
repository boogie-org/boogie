procedure F() returns () {
	var x : float;
	x := fp(1) + fp(1);
	assert x == fp(2);
}