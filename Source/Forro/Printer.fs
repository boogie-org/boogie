module ForroPrinter

open System
open Forro

let PrintField f =
    printf "."
    match f with
    | Head -> printf "head"
    | Tail -> printf "tail"
    | Valid -> printf "valid"

let PrintOp op =
    printf " "
    match op with
    | Eq -> printf "=="
    | Neq -> printf "!="
    | Plus -> printf "+"
    | Minus -> printf "-"
    | Times -> printf "*"
    | Less -> printf "<"
    | AtMost -> printf "<="
    | And -> printf "and"
    | Or -> printf "or"
    printf " "

let rec PrintExpr e outermost =
    match e with
    | Constant(x) -> printf "%i" x
    | Null -> printf "null"
    | Identifier(Var(x)) -> printf "%s" x
    | Not(e) -> printf "not(" ; PrintExpr e true ; printf ")"
    | Binary(op,a,b) ->
        if outermost then () else printf "("
        PrintExpr a false ; PrintOp op ; PrintExpr b false
        if outermost then () else printf ")"
    | Select(e,f) -> PrintExpr e false ; PrintField f
    | Old(e) -> printf "old(" ; PrintExpr e true ; printf ")"

let rec Indent n =
    if n = 0 then () else printf " " ; Indent (n-1)

let rec PrintStmt indent s =
    Indent indent
    let ind = indent + 2
    match s with
    | Assign(Var(x), e) -> printf "%s" x ; printf " := " ; PrintExpr e true
    | Update(obj,f,rhs) -> PrintExpr obj false ; PrintField f ; printf " := " ; PrintExpr rhs true
    | Alloc(Var(x),hd,tl) -> printf "%s" x ; printf " := new (" ; PrintExpr hd false ; printf ", " ; PrintExpr tl false ; printf ")"
    | IfStmt(guard,thn,els) ->
        printf "if " ; PrintExpr guard true ; printfn " then"
        PrintStmtList ind thn
        Indent indent ; printfn "else"
        PrintStmtList ind els
        Indent indent ; printf "end"
    | WhileStmt(guard,invs,body) ->
        printf "while " ; PrintExpr guard true ; printfn ""
        List.iter (fun inv -> Indent ind ; printf "invariant " ; PrintExpr inv true ; printfn "") invs
        Indent indent ; printfn "do"
        PrintStmtList ind body
        Indent indent ; printf "end"
    | CallStmt(outs,id,ins) ->
        printf "call "
        if outs.IsEmpty then () else
            ignore (List.fold (fun sep v -> printf "%s%s" sep (VarName v) ; ", ") "" outs) ; printf " :="
        printf " %s" id
        printf "("
        ignore (List.fold (fun sep e -> printf "%s" sep ; PrintExpr e false ; ", ") "" ins)
        printf ")"
    | Assert(e) ->
        printf "assert " ; PrintExpr e true
    printfn ";"

and PrintStmtList indent slist =
    match slist with
    | Block(ss) -> List.iter (fun s -> PrintStmt indent s) ss

let PrintProc p =
    match p with
    | Proc(name, ins, outs, req, ens, body) ->
        // signature
        printf "procedure "
        if outs.IsEmpty then () else
            ignore (List.fold (fun sep v -> printf "%s%s" sep (VarName v) ; ", ") "" outs) ; printf " :="
        printf " %s(" name
        ignore (List.fold (fun sep v -> printf "%s%s" sep (VarName v) ; ", ") "" ins)
        printfn ")"
        // specification
        printf "  requires "
        PrintExpr req true
        printfn ""
        printf "  ensures "
        PrintExpr ens true
        printfn ""
        // body
        printfn "do"
        PrintStmtList 2 body
        printfn "end;"

let rec PrintProcs ps =
    match ps with
    | [] -> ()
    | p::rest -> PrintProc p ; PrintProcs rest

let Print prog =
    match prog with
    | Prog(procs) -> PrintProcs procs
