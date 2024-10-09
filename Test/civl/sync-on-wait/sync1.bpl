// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var {:sync_on_wait} {:linear} {:layer 0,2} globalPerm: One int;

atomic action {:layer 2} mainAction({:linear_in} p: One int)
creates A_Inc;
{
    async call A_Inc(p);
}

yield procedure {:layer 1} main ({:linear_in} p: One int)
refines mainAction;
{  
  async call _A_Inc(p);
  call Yield();
  call _Wait(p->val);
}

yield invariant{:layer 1} Yield ();

async atomic action {:layer 1,2} A_Inc ({:sync_on_wait} {:linear_in} perm : One int)
modifies globalPerm;
{ 
 globalPerm := perm;
}

yield procedure {:layer 0} _A_Inc ({:sync_on_wait} {:linear} perm : One int);
refines A_Inc;

atomic action {:layer 1} Wait ({:sync_on_wait} X: int)
{
    assume X == globalPerm->val;
}

yield procedure {:layer 0} _Wait ({:sync_on_wait} X: int);
refines Wait;

// What about this program do you not understand?

// * In the async I cannot give p to another async directly but I can pass it's value or it directly to any other action that does not take it as linear.

// * I need to make globalPerm linear right?
// What does it mean if I don't make it linear. My whole purpose is that the permission passed is non duplicatable so I can send it to global but for that the global container needs to be a permission container too. 

// * but how does one pass permission to another variable, isn't that duplicating? you typically use Set_Put(scatter-gather-full) or something like this 
// In actions could it be that duplicating only happens when one passes it to PAs. or puts it in two globals maybe. 
// can you try the second one. Yeah this throws an error. ... I was interested in looking at the thing that fails and also the error is probably in the typechecker and hence the file was not generated.

// I think I am good. This makes sense.