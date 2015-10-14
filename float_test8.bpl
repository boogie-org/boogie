procedure F() returns () {
	var x : float;
	x := fp(0.1) + fp(0.1);
	assert x == fp(0.2);
}