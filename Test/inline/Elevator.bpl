// RUN: %boogie "%s" > "%t"
// RUN: %boogie -removeEmptyBlocks:0 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// A Boogie version of Elevator.asml (see Boogie/Test/inline/Elevator.asml)

var floors: [int]bool;  // set of integer
var DoorsOpen: [int]bool;
var liftDoorOpen: bool;
var liftLevel: int;
var moving: bool;
var headingTo: int;

procedure Main_Error()
  modifies floors, DoorsOpen, liftDoorOpen, liftLevel, moving, headingTo;
{
  var i: int;

  call Initialize();
  while (true)
    invariant !(liftDoorOpen && moving);
  {
    if (*) {
      havoc i;  call ButtonPress(i);
    } else if (*) {
      call MoveUp();
    } else if (*) {
      call MoveDown_Error();
    } else if (*) {
      call Stop();
    } else if (*) {
      call OpenLiftDoor();
    } else if (*) {
      call CloseLiftDoor();
    } else if (*) {
      havoc i;  call OpenFloorDoor(i);
    } else {
      havoc i;  call CloseFloorDoor(i);
    }
  }
}

procedure Main_Correct()
  modifies floors, DoorsOpen, liftDoorOpen, liftLevel, moving, headingTo;
{
  var i: int;

  call Initialize();
  while (true)
    invariant !(liftDoorOpen && moving);
  {
    if (*) {
      havoc i;  call ButtonPress(i);
    } else if (*) {
      call MoveUp();
    } else if (*) {
      call MoveDown_Correct();
    } else if (*) {
      call Stop();
    } else if (*) {
      call OpenLiftDoor();
    } else if (*) {
      call CloseLiftDoor();
    } else if (*) {
      havoc i;  call OpenFloorDoor(i);
    } else {
      havoc i;  call CloseFloorDoor(i);
    }
  }
}

procedure {:inline 1} Initialize()
  modifies floors, DoorsOpen, liftDoorOpen, liftLevel, moving, headingTo;
{
  DoorsOpen := EmptySet;
  liftDoorOpen := false;
  liftLevel := 1;
  moving := false;
  headingTo := 0;
}

procedure {:inline 1} ButtonPress(i: int)
  modifies headingTo;
{
  assume floors[i];
  headingTo := i;
}

procedure {:inline 1} MoveUp()
  modifies moving, liftLevel;
{
  assume !liftDoorOpen && liftLevel < headingTo;
  assume !DoorsOpen[liftLevel];
  moving := true;
  liftLevel:= liftLevel + 1;
}

procedure {:inline 1} MoveDown_Error()
  modifies moving, liftLevel;
{
  //bug, should require that liftDoorOpen = false
  // assume !liftDoorOpen;
  assume liftLevel > headingTo && headingTo > 0;
  assume !DoorsOpen[liftLevel];
  moving := true;
  liftLevel := liftLevel - 1;
}

procedure {:inline 1} MoveDown_Correct()
  modifies moving, liftLevel;
{
  assume !liftDoorOpen;
  assume liftLevel > headingTo && headingTo > 0;
  assume !DoorsOpen[liftLevel];
  moving := true;
  liftLevel := liftLevel - 1;
}

procedure {:inline 1} Stop()
  modifies moving;
{
  assume liftLevel == headingTo;
  moving := false;
}
  
procedure {:inline 1} OpenLiftDoor()
  modifies liftDoorOpen;
{
  assume !moving;
  liftDoorOpen := true;
}
  
procedure {:inline 1} CloseLiftDoor()
  modifies liftDoorOpen;
{
  liftDoorOpen := false;
}

procedure {:inline 1} OpenFloorDoor(i: int)
  modifies DoorsOpen;
{
  assume liftLevel == i;
  DoorsOpen[i] := true;  // DoorsOpen := DoorsOpen union {i};
}

procedure {:inline 1} CloseFloorDoor(i: int)
  modifies DoorsOpen;
{
  DoorsOpen[i] := false;  // DoorsOpen := DoorsOpen - {i}
}

// ---------------------------------------------------------------

const EmptySet: [int]bool;
axiom (forall o: int :: { EmptySet[o] } !EmptySet[o]);

// ---------------------------------------------------------------
