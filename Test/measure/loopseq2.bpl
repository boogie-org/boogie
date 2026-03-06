// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;


procedure one() 
{
    var n: int;
    n := 10;
    while(n >= 1)
    measure n;
    {
        n := n - 1;
    }
}



// Suppose we introduce a measure command: so the measure command it's structure is that
// is a list of expressions - which are typechecked to int;
// measure n1, n2 ... n_n;

// At the time of converting str to unstr, when inv are converted to asserts in the loop header, we convert measure in loop header to this measure command. 


// The loop becomes yield-free at some layer and then it remains yield free
// There is a layer in the typechecker you can find.
// You need a measure from this layer to the disappering layer -> right now assume the layer is eq to disap layer.



// Ideas

// 1. NOthing wrong with a measure command being exposed. (in the body of the procedure in the desugared file)
// one way to give meanign to it - say that you record the measure attribute, then you arrive at the next measure you check that it decreased. 
// It does not mean anythign in hte proc declaration, but only in the body it has this meaning. 

// 2. Have a measure command that will be parsed, but we ignore the measure command if it is not in the loop head. 

// To do this we have to add it in the parser. 

// we drop it in the measure checker  or we can report an error in the typechecking phase in the measure checker

// 3. 

// conundrum about yield procedures calling mover procedures.

// why do we require their layers are the same? 

// the answer is - Let A call B(mover)
// A layer is 3 and B layer is 1
// the problem is that I won't be able to define the body of at layer 2. 

// Because the mover procedure doesn't exist at layer 2. 

// why does this not pop up when you have a loop, because inside the loop body is inlined. there is afeature in civl that may change the body, the body will not change. 
// but civl has a feature called action refinement, and because of this a loop 

// mover procedure has no definition after its layer so we have a layer 


// failure are termination.  - threads don't starve (one way of defining fairness). 
// What good is just doing fair termination. 

// All fair executions terminate.

// we want to prove that there is no fair infinite execution.

// example: why would it be useful for me to know that this program fair terminates. 
// Trieber stack - pushes and pops can fail. 
// I wanted to prove that it can make progress even with infinite retry. 

// I think this one also have - starvation free 

// what if in the presence of retries. that it is an intelligent retry. 
// how to capture the difference between intelligent retry and buggy retry. 

// doesn't depend 
// informally show that supposing the write does not interfere with the snapshot infinitely often, then every snapshot will come to a conclusion. 

// formally this would be linear temporal logic formula - one way

// next question is ... what good is proving only one way of fair termination. 
// have patience, you must to do addition before multiplication. 


// progress conditions on lock free algorithms. - progress specifications for non-blocking algorithms.

// in general even there the notion of fairness, it is going to be more sophisticated than the basic things. 
// my hunch , by adding extra ghost state you should be able to convert all of those into the vanilla fairness specification. 


