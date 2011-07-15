// BEGIN INJECTED CODE

procedure UpdateNavigation(uri:Ref);
implementation UpdateNavigation(uri:Ref) {
    CurrentNavigationPage := uri;
}

procedure DriveControls();
implementation DriveControls() {
  var isCurrentPage1: bool;
  var isCurrentPage2: bool;
  var isCurrentPage3: bool;
  var isCurrentPage4: bool;

  // TODO there can be parameters in the URI and other stuff that makes this checks quite unreliable
  call isCurrentPage1 := System.String.op_Equality$System.String$System.String(CurrentNavigationPage, $string_literal_$Page1.xaml_0);
  call isCurrentPage2 := System.String.op_Equality$System.String$System.String(CurrentNavigationPage, $string_literal_$Page2.xaml_1);
  call isCurrentPage3 := System.String.op_Equality$System.String$System.String(CurrentNavigationPage, $string_literal_$Page3.xaml_2);
  call isCurrentPage4 := System.String.op_Equality$System.String$System.String(CurrentNavigationPage, $string_literal_$Page4.xaml_3);
  
  if (isCurrentPage1) {
    call drivePage1Controls();
  } else if (isCurrentPage2) {
    call drivePage2Controls();
  } else if (isCurrentPage3) {
    call drivePage3Controls();
  } else if (isCurrentPage4) {
    call drivePage4Controls();
  }
}

procedure drivePage1Controls();
implementation drivePage1Controls() {
  var $continueOnPage: bool;
  var $activeControl: int;
  var $control: Ref;
  var $isEnabledRef: Ref;
  var $isEnabled: bool;

  $continueOnPage:=true;
  havoc $activeControl;
  while ($continueOnPage) {
      if ($activeControl==0) {
        // radio1 check
        $control := SimpleNavigationApp.Page1.radioButton1[$page1];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==1) {
        // radio2 check
        $control := SimpleNavigationApp.Page1.radioButton2[$page1];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==2) {
        // radio3 check
        $control := SimpleNavigationApp.Page1.radioButton3[$page1];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==3) {
        //radio4 check
        $control := SimpleNavigationApp.Page1.radioButton4[$page1];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==4) {
        //button click
        $control := SimpleNavigationApp.Page1.btnNavigate[$page1];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call SimpleNavigationApp.Page1.btnNavigate_Click$System.Object$System.Windows.RoutedEventArgs($page1, null, null);
          $continueOnPage := false;
        }
    }
  }
}

procedure drivePage2Controls();
implementation drivePage2Controls() {
  var $continueOnPage: bool;
  var $activeControl: int;
  var $control: Ref;
  var $isEnabledRef: Ref;
  var $isEnabled: bool;

  $continueOnPage:=true;
  havoc $activeControl;
  while ($continueOnPage) {
      if ($activeControl==0) {
        // radio1 check
        $control := SimpleNavigationApp.Page2.radioButton1[$page2];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==1) {
        // radio2 check
        $control := SimpleNavigationApp.Page2.radioButton2[$page2];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==2) {
        // radio3 check
        $control := SimpleNavigationApp.Page2.radioButton3[$page2];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==3) {
        //radio4 check
        $control := SimpleNavigationApp.Page2.radioButton4[$page2];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==4) {
        //button click
        $control := SimpleNavigationApp.Page2.btnNavigate[$page2];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call SimpleNavigationApp.Page2.btnNavigate_Click$System.Object$System.Windows.RoutedEventArgs($page2, null, null);
          $continueOnPage := false;
        }
    }
  }
}

procedure drivePage3Controls();
implementation drivePage3Controls() {
  var $continueOnPage: bool;
  var $activeControl: int;
  var $control: Ref;
  var $isEnabledRef: Ref;
  var $isEnabled: bool;

  $continueOnPage:=true;
  havoc $activeControl;
  while ($continueOnPage) {
      if ($activeControl==0) {
        // radio1 check
        $control := SimpleNavigationApp.Page3.radioButton1[$page3];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==1) {
        // radio2 check
        $control := SimpleNavigationApp.Page3.radioButton2[$page3];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==2) {
        // radio3 check
        $control := SimpleNavigationApp.Page3.radioButton3[$page3];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==3) {
        //radio4 check
        $control := SimpleNavigationApp.Page3.radioButton4[$page3];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==4) {
        //button click
        $control := SimpleNavigationApp.Page3.btnNavigate[$page3];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call SimpleNavigationApp.Page3.btnNavigate_Click$System.Object$System.Windows.RoutedEventArgs($page3, null, null);
          $continueOnPage := false;
        }
    }
  }
}

procedure drivePage4Controls();
implementation drivePage4Controls() {
  var $continueOnPage: bool;
  var $activeControl: int;
  var $control: Ref;
  var $isEnabledRef: Ref;
  var $isEnabled: bool;

  $continueOnPage:=true;
  havoc $activeControl;
  while ($continueOnPage) {
      if ($activeControl==0) {
        // radio1 check
        $control := SimpleNavigationApp.Page4.radioButton1[$page4];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==1) {
        // radio2 check
        $control := SimpleNavigationApp.Page4.radioButton2[$page4];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==2) {
        // radio3 check
        $control := SimpleNavigationApp.Page4.radioButton3[$page4];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==3) {
        //radio4 check
        $control := SimpleNavigationApp.Page4.radioButton4[$page4];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call System.Windows.Controls.Primitives.ToggleButton.set_IsChecked$System.Nullable$System.Boolean$($control, Box2Ref(Bool2Box(true)));
        }
      } else if ($activeControl==4) {
        //button click
        $control := SimpleNavigationApp.Page4.btnNavigate[$page4];
        call $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);
        $isEnabled := Box2Bool(Ref2Box($isEnabledRef));
        if ($isEnabled) {
          call SimpleNavigationApp.Page4.btnNavigate_Click$System.Object$System.Windows.RoutedEventArgs($page4, null, null);
          $continueOnPage := false;
        }
    }
  }
}

var $page1: Ref;
var $page2: Ref;
var $page3: Ref;
var $page4: Ref;

procedure SimpleNavigationApp.Main();
implementation SimpleNavigationApp.Main() {
  var $doWork: bool;
  var $activeControl: int;
  var $isEnabledRef: Ref;
  var $isEnabled: bool;
  var $control: Ref;

  call SimpleNavigationApp.Page1.#ctor($page1);
  call SimpleNavigationApp.Page2.#ctor($page2);
  call SimpleNavigationApp.Page3.#ctor($page3);
  call SimpleNavigationApp.Page4.#ctor($page4);
  call SimpleNavigationApp.Page1.Page1_Loaded$System.Object$System.Windows.RoutedEventArgs($page1, null, null);

  CurrentNavigationPage := $string_literal_$Page1.xaml_0;

  havoc $doWork;
  while ($doWork) {
    call DriveControls();
    havoc $doWork; 
  }
}

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

var CurrentNavigationPage: Ref;
var uriToNavigate: Ref;

// END INJECTED CODE