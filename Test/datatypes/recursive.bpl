// RUN: %parallel-boogie /lib:base "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List { 
    List(
        data: int,
        next: Option (Cell (Loc List) List)
    )
}

procedure append(l: List, m: List) returns (l': List)
{
    var data: int;
    var next: Option (Cell (Loc List) List);
    var cell: Cell (Loc List) List;
    var loc_p: One (Loc List);
    var tl, tl': List;

    List(data, next) := l;
    
    if (next == Some(cell)) 
    { Cell(loc_p, tl) := cell; call tl' := append(tl, m); cell := Cell(loc_p, tl'); }
    else
    { call loc_p := Loc_New(); cell := Cell(loc_p, m); }
    
    next := Some(cell);
    l' := List(data, next);
}
