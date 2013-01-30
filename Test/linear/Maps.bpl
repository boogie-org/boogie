type X;

function {:builtin "MapAdd"} MapAdd([X]int, [X]int) : [X]int;
function {:builtin "MapSub"} MapSub([X]int, [X]int) : [X]int;
function {:builtin "MapMul"} MapMul([X]int, [X]int) : [X]int;
function {:builtin "MapDiv"} MapDiv([X]int, [X]int) : [X]int;
function {:builtin "MapMod"} MapMod([X]int, [X]int) : [X]int;
function {:builtin "MapConst"} MapConstInt(int) : [X]int;
function {:builtin "MapConst"} MapConstBool(bool) : [X]bool;
function {:builtin "MapAnd"} MapAnd([X]bool, [X]bool) : [X]bool;
function {:builtin "MapOr"} MapOr([X]bool, [X]bool) : [X]bool;
function {:builtin "MapNot"} MapNot([X]bool) : [X]bool;
function {:builtin "MapIte"} MapIteInt([X]bool, [X]int, [X]int) : [X]int;
function {:builtin "MapIte"} MapIteBool([X]bool, [X]bool, [X]bool) : [X]bool;
function {:builtin "MapLe"} MapLe([X]int, [X]int) : [X]bool;
function {:builtin "MapLt"} MapLt([X]int, [X]int) : [X]bool;
function {:builtin "MapGe"} MapGe([X]int, [X]int) : [X]bool;
function {:builtin "MapGt"} MapGt([X]int, [X]int) : [X]bool;
function {:builtin "MapEq"} MapEq([X]int, [X]int) : [X]bool;
function {:builtin "MapIff"} MapIff([X]bool, [X]bool) : [X]bool;
function {:builtin "MapImp"} MapImp([X]bool, [X]bool) : [X]bool;



