// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:sync_on_wait} {:linear} {:layer 0,2} globalPerm: Set int;

atomic action {:layer 2} ServiceAction({:linear_in} p: Set int)
// creates A_Inc;
{
    // async call A_Inc(p);
}

yield procedure {:layer 1} Service ({:sync_on_wait} {:linear_in} p: Set int)
refines ServiceAction;
{  
  async call {:sync_on_wait} _A_Inc(p);
  call Yield();
  call _Wait(p);
}

yield invariant{:layer 1} Yield ();

async atomic action {:layer 1,2} A_Inc ({:sync_on_wait} {:linear_in} perm : Set int)
modifies globalPerm;
{ 
 globalPerm := perm;
}

yield procedure {:layer 0} _A_Inc ({:sync_on_wait} {:linear_in} perm : Set int);
refines A_Inc;

atomic action {:layer 1} Wait ({:sync_on_wait} X: Set int)
{
    assume Set_IsSubset(X, globalPerm);
}

yield procedure {:layer 0} _Wait ({:sync_on_wait} X: Set int);
refines Wait;


