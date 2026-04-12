// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List { 
    List(
        data: int,
        next: Option (Cell Loc List)
    )
}

procedure append({:linear_in} l: List, {:linear_in} m: List) returns ({:linear} l': List)
{
    var data: int;
    var next: Option (Cell Loc List);
    var cell: Cell Loc List;
    var loc_p: One Loc;
    var tl, tl': List;

    List(data, next) := l;
    
    if (next is Some)
    { Some(cell) := next; Cell(loc_p, tl) := cell; call tl' := append(tl, m); cell := Cell(loc_p, tl'); }
    else
    { call loc_p := Loc_New(); cell := Cell(loc_p, m); }
    
    next := Some(cell);
    l' := List(data, next);
}
