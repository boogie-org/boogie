module Translator

open Forro
open BoogieAst
open Resolver
open System.Collections.Generic

let rec Append a b =
    match a with
    | [] -> b
    | hd::tl -> hd::(Append tl b)

let rec Flatten a =
    match a with
    | [] -> []
    | list::rest -> Append list (Flatten rest)

// ---------- Prelude ----------

let Prelude =
    @"// Forro

var $head: [int]int;  // int -> int
var $tail: [int]int;
var $valid: [int]bool;  // array int of bool

const null: int;

function GoodState([int]int, [int]int, [int]bool): bool;

axiom (forall hd, tl: [int]int, valid: [int]bool ::
        { GoodState(hd, tl, valid) }
        GoodState(hd, tl, valid) ==> !valid[null]);
"

// ---------- Translate Expressions ----------

let TrField f =
    match f with
    | Head -> "$head"
    | Tail -> "$tail"
    | Valid -> "$valid"

let AllFields = ["$head" ; "$tail" ; "$valid"]

let MkPred term =
    match term with
    | BToTerm(p) -> p
    | _ -> BToPred(term)

let MkTerm pred =
    match pred with
    | BToPred(e) -> e
    | _ -> BToTerm(pred)

let rec TrExpr expr =
    match expr with
    | Constant(x) -> BConstant x
    | Null -> BNull
    | Identifier(Var(x)) -> BIdentifier(x)
    | Not(e) -> BNot(TrExpr e)
    | Binary(op,a,b) ->
        let a = TrExpr a
        let b = TrExpr b
        match op with
        | Eq -> MkTerm(BBinary(BEq,a,b))
        | Neq -> MkTerm(BBinary(BNeq,a,b))
        | Plus -> BBinary(BPlus,a,b)
        | Minus -> BBinary(BMinus,a,b)
        | Times -> BBinary(BTimes,a,b)
        | Less -> MkTerm(BBinary(BLess,a,b))
        | AtMost -> MkTerm(BBinary(BAtMost,a,b))
        | And -> MkTerm(BBinary(BAnd, MkPred a, MkPred b))
        | Or -> MkTerm(BBinary(BOr, MkPred a, MkPred b))
    | Select(e,f) ->
        let r = BSelect(TrField f, TrExpr e)
        if f = Field.Valid then MkTerm(r) else r
    | Old(e) -> BOld(TrExpr e)

let rec ListToConjunction list =
    match list with
    | [] -> BTrue
    | [P] -> P
    | hd::tl -> BBinary(BAnd, hd, ListToConjunction tl)

let rec DefL expr =
    match expr with
    | Constant(x) -> []
    | Null -> []
    | Identifier(Var(x)) -> []
    | Not(e) -> DefL e
    | Binary(op,a,b) ->
        match op with
        | And -> BBinary(BOr, BNot(MkPred (TrExpr a)), Def b) :: (DefL a)   // (Def a) && ((TrExpr a) ==> (Def b))
        | Or -> BBinary(BOr, MkPred (TrExpr a), Def b) :: (DefL a)  // (Def a) && (!(TrExpr a) ==> (Def b))
        | _ -> Append (DefL b) (DefL a)
    | Select(e,f) ->
        let def = DefL e
        if f = Field.Valid then def  // it is always okay to ask about .valid
        else BSelect("$valid", TrExpr e) :: def
    | Old(e) -> List.map BOld (DefL e)

and Def expr =
    ListToConjunction (List.rev (DefL expr))

let AssumeGoodState =
    BAssume (BFunc("GoodState", List.map BIdentifier AllFields))

// ---------- Translate Statements ----------

type LocalBookkeeping = LB of int * BVarDecl list

let FreshLocal locals =
    match locals with
    | LB(n, vars) ->
        let name = "nw$" + n.ToString()
        (BIdentifier(name), name, LB(n+1, BVar(name, BInt)::vars))

let rec TrStmt stmt locals =
    match stmt with
    | Assign(v,e) ->
        let s = [ BAssert (Def e) ;
                  BAssign(VarName v, TrExpr e) ]
        (s, locals)
    | Update(obj,f,rhs) ->
        let o = TrExpr obj
        let s = [ BAssert(Def obj) ; BAssert (Def rhs) ;
                  BAssert(BSelect("$valid", o)) ;
                  BUpdate(TrField f, o, if f = Field.Valid then MkPred(TrExpr rhs) else TrExpr rhs) ;
                  AssumeGoodState ]
        (s, locals)
    | Alloc(v,hd,tl) ->
        let nw, name, locals = FreshLocal locals
        let s = [ BAssert (Def hd) ; BAssert (Def tl) ;
                  BHavoc [name] ;
                  BAssume(BNot(BSelect("$valid", nw))) ;
                  BAssume(BBinary(BEq, BSelect("$head", nw), TrExpr hd)) ;
                  BAssume(BBinary(BEq, BSelect("$tail", nw), TrExpr tl)) ;
                  BUpdate("$valid", nw, BTrue) ;
                  AssumeGoodState ;
                  BAssign(VarName v, nw) ]
        (s, locals)
    | IfStmt(guard,thn,els) ->
        let check = BAssert(Def guard)
        let thn, locals = TrStmtList thn locals
        let els, locals = TrStmtList els locals
        let s = BIfStmt(MkPred (TrExpr guard), thn, els)
        ([check ; s], locals)
    | WhileStmt(guard,invs,body) ->
        let ii = [Def guard]
        let ii = List.fold (fun ii -> fun inv -> (MkPred (TrExpr inv))::(Def inv)::ii) ii invs
        let s, locals = TrStmtList body locals
        match s with
        | BBlock(slist) ->
            ([BWhileStmt(MkPred (TrExpr guard), List.rev ii, BBlock(AssumeGoodState::slist)) ; AssumeGoodState], locals)
    | CallStmt(outs,id,ins) ->
        let check = List.map (fun e -> BAssert (Def e)) ins
        let ins = List.map (fun e -> TrExpr e) ins
        let outs = List.map (fun p -> VarName p) outs
        let s = BCallStmt(outs, id + "#Proc", ins)
        (Append check [s ; AssumeGoodState ], locals)
    | Assert(e) ->
        ([ BAssert (Def e) ; BAssert (MkPred (TrExpr e)) ], locals)

and TrStmtList slist locals =
    match slist with
    | Block([]) -> (BBlock [], locals)
    | Block(s::rest) ->
        let s,locals = TrStmt s locals
        let rest,locals = TrStmtList (Block rest) locals
        match rest with
        | BBlock(slist) -> (BBlock(Append s slist), locals)

// ---------- Translate Procedure Body ----------

let TrSignature ins outs =
    let bIns = List.map (fun v -> BVar(VarName v, BInt)) ins
    let bOuts = List.map (fun v -> BVar(VarName v, BInt)) outs
    (bIns, bOuts)

let LocalDecls (vars: Dictionary<string,VarKind>) =
    Flatten [ for kv in vars -> if kv.Value = VarKind.Local then [BVar(kv.Key, BInt)] else [] ]

let TrProc proc vars =
    match proc with
    | Proc(id, ins, outs, req, ens, body) ->
        let bIns, bOuts = TrSignature ins outs
        let pre = MkPred (TrExpr req)
        let post = MkPred (TrExpr ens)
        let locals = LocalDecls vars
        let b, locals = TrStmtList body (LB(0,locals))
        match b, locals with
        | BBlock(slist), LB(n, vars) ->
            BProc(id + "#Proc", bIns, bOuts, pre, AllFields, post,
               List.rev vars, BBlock(AssumeGoodState::slist))

// --------------------

let TrSpec proc vars =
    match proc with
    | Proc(id, ins, outs, req, ens, body) ->
        let bIns, bOuts = TrSignature ins outs
        let b = [ AssumeGoodState ;
                  BAssert (Def req) ; BAssume (MkPred (TrExpr req)) ;
                  BHavoc AllFields ; AssumeGoodState ;
                  BAssert (Def ens) ]
        BProc(id + "#WellFormedSpec", bIns, bOuts, BTrue, AllFields, BTrue, [], BBlock(b))

let TrProcedure rproc =
    match rproc with
    | proc, (vars: Dictionary<string,VarKind>) ->
        let name = ProcedureName proc
        (TrSpec proc vars, TrProc proc vars)

let Translate (rprog: (Procedure * Dictionary<string,VarKind>) list) =
    let procs = List.fold (fun list -> fun (p,q) -> p::q::list) [] (List.map TrProcedure rprog)
    BProg(Prelude, procs)
