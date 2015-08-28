module Resolver

open System
open Forro

exception ResolutionError of string

let ResolutionError(s: string) =
    raise (ResolutionError s)

type VarKind = InParam | OutParam | Local

type Context(procedures: Collections.Generic.IDictionary<string,Procedure>) =
    let mutable locals = null
    let mutable ProcName = ""
    member c.Procedures = procedures
    member c.StartNewProcedure procName =
        ProcName <- procName
        locals <- new Collections.Generic.Dictionary<string,VarKind>()
    member c.AddLocal v kind =
        let name = VarName v
        if locals.ContainsKey name then ResolutionError ("duplicate variable '" + name + "' in procedure '" + ProcName + "'") else ()
        locals.Add(name, kind)
    member c.HasLocal v =
        locals.ContainsKey (VarName v)
    member c.IncludeAssignmentTarget v =
        let name = VarName v
        if locals.ContainsKey name then
            let kind = locals.Item name
            if kind = VarKind.InParam then ResolutionError ("variable '"+ name + "' is an in-parameter, which cannot be used as an assignment target") else ()
        else
            locals.Add(name, VarKind.Local)
    member v.GetLocals = locals

let rec ResolveExpr (ctx: Context) expr twoState specContext =
    match expr with
    | Constant(x) -> ()
    | Null -> ()
    | Identifier(v) ->
        if ctx.HasLocal v then () else ResolutionError ("undefined variable: " + VarName v)
    | Not(e) -> ResolveExpr ctx e twoState specContext
    | Binary(op,a,b) ->
        ResolveExpr ctx a twoState specContext
        ResolveExpr ctx b twoState specContext
    | Select(e,f) ->
        ResolveExpr ctx e twoState specContext
        match f with
        | Valid -> if specContext then () else ResolutionError "valid can only be used in specification contexts"
        | _ -> ()
    | Old(e) ->
        if twoState then () else ResolutionError "old expressions can only be used in two-state contexts"
        ResolveExpr ctx e twoState specContext

let rec ResolveStmt ctx s =
    match s with
    | Assign(v, e) ->
        ResolveExpr ctx e false false
        ctx.IncludeAssignmentTarget v
    | Update(obj,f,rhs) ->
        ResolveExpr ctx obj false false
        match f with
        | Valid -> ResolutionError "valid can only be used in specification contexts (in particular, it cannot be assigned to)"
        | _ -> ()
        ResolveExpr ctx rhs false false
    | Alloc(v,hd,tl) ->
        ResolveExpr ctx hd false false
        ResolveExpr ctx tl false false
        ctx.IncludeAssignmentTarget v
    | IfStmt(guard,thn,els) ->
        ResolveExpr ctx guard false false
        ResolveStmtList ctx thn
        ResolveStmtList ctx els
    | WhileStmt(guard,invs,body) ->
        ResolveExpr ctx guard false false
        List.iter (fun inv -> ResolveExpr ctx inv true true) invs
        ResolveStmtList ctx body
    | CallStmt(outs,name,ins) ->
        if ctx.Procedures.ContainsKey name then () else ResolutionError ("call to undefined procedure: " + name)
        match ctx.Procedures.Item name with
        | Proc(_,fIns,fOuts,_,_,_) ->
            if fIns.Length = ins.Length then () else ResolutionError ("call to " + name + " has wrong number of in-parameters (got " + ins.Length.ToString() + ", expected " + fIns.Length.ToString() + ")")
            if fOuts.Length = outs.Length then () else ResolutionError ("call to " + name + " has wrong number of out-parameters (got " + outs.Length.ToString() + ", expected " + fOuts.Length.ToString() + ")")
        List.iter (fun e -> ResolveExpr ctx e false false) ins
        let outnames = new Collections.Generic.Dictionary<string,Variable>()
        List.iter (fun v ->
            ctx.IncludeAssignmentTarget v
            let name = VarName v
            if outnames.ContainsKey name then ResolutionError ("an actual out-parameter is allowed only once for a call: " + name) else ()
            outnames.Add(name, v)
            ) outs
    | Assert(e) ->
        ResolveExpr ctx e true true

and ResolveStmtList ctx slist =
    match slist with
    | Block(ss) -> List.iter (fun s -> ResolveStmt ctx s) ss

let ProcedureName p =
    match p with Proc(id,_,_,_,_,_) -> id

let ResolveProc (ctx: Context) p =
    match p with
    | Proc(name, ins, outs, req, ens, body) ->
        // look up 'name' in ctx.Procedures, report an error if it is not 'p'
        let q = ctx.Procedures.Item name
        if p <> q then ResolutionError ("duplicate procedure: " + name) else ()
        ctx.StartNewProcedure name
        // look for duplicates in ins+outs
        List.iter (fun v -> ctx.AddLocal v VarKind.InParam) ins
        List.iter (fun v -> ctx.AddLocal v VarKind.OutParam) outs
        // resolve specification
        ResolveExpr ctx req false true
        ResolveExpr ctx ens true true
        // resolve body
        ResolveStmtList ctx body
        ctx.GetLocals

let Resolve prog =
    match prog with
    | Prog(procs) ->
        let procedures = dict [ for p in procs -> ProcedureName p, p ]
        let ctx = Context(procedures)
        List.map (fun p -> p, ResolveProc ctx p) procs
