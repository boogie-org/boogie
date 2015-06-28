module Forro

type Field = Head | Tail | Valid

type Variable = Var of string

let VarName v =
    match v with Var(x) -> x

type Operator = Eq | Neq | Plus | Minus | Times
              | Less | AtMost | And | Or

type Expression =
    | Constant of int
    | Null
    | Identifier of Variable
    | Not of Expression
    | Binary of Operator * Expression * Expression
    | Select of Expression * Field
    | Old of Expression

type Statement =
    | Assign of Variable * Expression
    | Update of Expression * Field * Expression
    | Alloc of Variable * Expression * Expression
    | IfStmt of Expression * StmtList * StmtList
    | WhileStmt of Expression * Expression list * StmtList
    | CallStmt of Variable list * string * Expression list
    | Assert of Expression

and StmtList  =
    Block of Statement list

type Procedure =
    Proc of string * Variable list * Variable list * Expression * Expression * StmtList

type Program =
    Prog of Procedure list
