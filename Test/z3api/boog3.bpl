type ref;
type Wicket;

procedure Dummy();
implementation Dummy() {
  var x: Wicket;
  assert (x!=x);
}