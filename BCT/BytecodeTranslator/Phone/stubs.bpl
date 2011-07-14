function isControlEnabled(Ref) : bool;
function isControlChecked(Ref) : bool;

procedure System.String.op_Equality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool);
procedure System.String.op_Inequality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool);

implementation System.String.op_Equality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool) {
  $result := (a$in == b$in);
}

implementation System.String.op_Inequality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool) {
  $result := (a$in != b$in);
}

procedure System.Windows.Controls.Control.set_IsEnabled$System.Boolean($this: Ref, value$in: bool);
implementation System.Windows.Controls.Control.set_IsEnabled$System.Boolean($this: Ref, value$in: bool) {
  assume isControlEnabled($this) == value$in;
}

procedure System.Windows.Controls.Control.get_IsEnabled($this: Ref) returns ($result: Ref);
implementation System.Windows.Controls.Control.get_IsEnabled($this: Ref) returns ($result: Ref) {
  var enabledness: bool;
  enabledness := isControlEnabled($this);
  $result := Box2Ref(Bool2Box(enabledness));
}

procedure System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($this: Ref, value$in: Ref);
implementation System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($this: Ref, value$in: Ref) {
  var check: bool;

  check := Box2Bool(Ref2Box(value$in));
  assume isControlChecked($this) == check;
}

procedure System.Windows.Controls.Primitives.ToggleButton.get_IsChecked($this: Ref) returns ($result: Ref);
implementation System.Windows.Controls.Primitives.ToggleButton.get_IsChecked($this: Ref) returns ($result: Ref) {
  var isChecked: bool;
  isChecked := isControlChecked($this);
  $result := Box2Ref(Bool2Box(isChecked));
}

