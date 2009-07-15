
type C;

const c1:C;
const c2:C extends c1;
const c0:C extends a;         // error: parent of wrong type

const a:int;
