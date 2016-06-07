module BoogiePrinter

open ForroPrinter  // to get Indent
open BoogieAst

let PrintWithSep Pr sep list =
    ignore (List.fold (fun sp e -> printf "%s" sp ; Pr e ; sep) "" list)

let TypeName t =
    match t with
    | BInt -> "int"
    | BBool -> "bool"

let PrVarType v =
    match v with
    | BVar(name,t) ->
        printf "%s: %s" name (TypeName t)

let PrintOp op =
    printf " "
    match op with
    | BEq -> printf "=="
    | BNeq -> printf "!="
    | BPlus -> printf "+"
    | BMinus -> printf "-"
    | BTimes -> printf "*"
    | BLess -> printf "<"
    | BAtMost -> printf "<="
    | BAnd -> printf "&&"
    | BOr -> printf "||"
    printf " "

let rec PrintExpr e =
    match e with
    | BConstant(x) -> printf "%d" x
    | BFalse -> printf "false"
    | BTrue -> printf "true"
    | BNull -> printf "null"
    | BIdentifier(id) -> printf "%s" id
    | BNot(e) -> printf "!(" ; PrintExpr e ; printf ")"
    | BBinary(op,e0,e1) -> printf "(" ; PrintExpr e0 ; PrintOp op ; PrintExpr e1 ; printf ")"
    | BSelect(var,e) -> printf "%s[" var ; PrintExpr e ; printf "]"
    | BToPred(e) -> printf "(" ; PrintExpr e ; printf " != 0)"
    | BToTerm(e) -> printf "(if " ; PrintExpr e ; printf " then 1 else 0)"
    | BOld(e) -> printf "old(" ; PrintExpr e ; printf ")"
    | BFunc(id,args) -> printf "%s(" id ; PrintWithSep PrintExpr ", " args ; printf ")"

let rec PrintStmt indent stmt =
    Indent indent
    let ind = indent + 2
    match stmt with
    | BAssign(id,e) -> printf "%s := " id ; PrintExpr e ; printfn ";"
    | BUpdate(id,obj,rhs) -> printf "%s[" id ; PrintExpr obj ; printf "] := " ; PrintExpr rhs ; printfn ";"
    | BHavoc(ids) -> printf "havoc " ; PrintWithSep (printf "%s") ", " ids ; printfn ";"
    | BAssert(e) -> printf "assert " ; PrintExpr e ; printfn ";"
    | BAssume(e) -> printf "assume " ; PrintExpr e ; printfn ";"
    | BIfStmt(e,thn,els) ->
        printf "if (" ; PrintExpr e ; printfn ") {"
        PrintStmtList ind thn
        Indent indent
        printfn "} else {"
        PrintStmtList ind els
        Indent indent
        printfn "}"
    | BWhileStmt(e, invs, body) ->
        printf "while (" ; PrintExpr e ; printfn ")"
        List.iter (fun inv -> Indent ind ; printf "invariant " ; PrintExpr inv ; printfn ";") invs
        Indent indent
        printfn "{"
        PrintStmtList ind body
        Indent indent
        printfn "}"
    | BCallStmt(outs, id, ins) ->
        printf "call "
        if outs.IsEmpty then () else PrintWithSep (fun p -> printf "%s" p) ", " outs ; printf " := "
        printf "%s(" id
        PrintWithSep PrintExpr ", " ins
        printfn ");"

and PrintStmtList indent stmts =
    match stmts with
    | BBlock(slist) -> List.iter (fun s -> PrintStmt indent s) slist

let BPrintProc proc =
    match proc with
    | BProc(name, ins, outs, req, frame, ens, locals, body) ->
        printfn ""
        printf "procedure %s(" name
        PrintWithSep PrVarType ", " ins
        printf ") returns ("
        PrintWithSep PrVarType ", " outs
        printfn ")"
        printf "  requires "
        PrintExpr req
        printfn ";"
        printf "  modifies "
        PrintWithSep (printf "%s") ", " frame
        printfn ";"
        printf "  ensures "
        PrintExpr ens
        printfn ";"
        printfn "{"
        List.iter (fun local -> printf "  var " ; PrVarType local ; printfn ";") locals
        if locals.IsEmpty then () else printfn ""
        PrintStmtList 2 body
        printfn "}"

let BPrint (prog: BProgram) =
    match prog with
    | BProg(prelude, procs) ->
        printfn "%s" prelude
        List.iter BPrintProc procs
