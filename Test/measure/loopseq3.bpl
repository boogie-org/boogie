// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

var x: int;

procedure one() 
measure x;
modifies x;
{
    if (x <= 1){
        return;
    }

        x := x - 1;
        call one();
}



// // RUN: %parallel-boogie "%s" > "%t"
// // RUN: %diff "%s.expect" "%t"

// var x: int;
// var y: int;
// var z: bool;

// procedure one(tid: int)
// measure x;
// modifies x;
// {
//     if (x <= 0){
//         return; 
//     }
//     x := x - 1; 
//     call one(2);
// }

