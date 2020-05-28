// Parallel call that splits up into left and right movers

// procedure foo ()
// {
//   par [ x := x + 1] || [x := x - 1] || ... || [ x := x + 1]
//   [ x := x + 1]
// }
// refines [x := x + 2]
