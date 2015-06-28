namespace BoogieAst

type BType = BInt | BBool

type BOperator = BEq | BNeq | BPlus | BMinus | BTimes | BLess | BAtMost | BAnd | BOr

type BExpression =
    | BConstant of int
    | BFalse
    | BTrue
    | BNull
    | BIdentifier of string
    | BNot of BExpression
    | BBinary of BOperator * BExpression * BExpression
    | BSelect of string * BExpression
    | BToPred of BExpression    // BToPred(e) == (e != 0)
    | BToTerm of BExpression    // BToTerm(e) == (if e then 1 else 0)
    | BOld of BExpression
    | BFunc of string * BExpression list

type BStmtList  =
    BBlock of Statement list

and Statement =
    | BAssign of string * BExpression
    | BUpdate of string * BExpression * BExpression
    | BHavoc of string list
    | BAssert of BExpression
    | BAssume of BExpression
    | BIfStmt of BExpression * BStmtList * BStmtList
    | BWhileStmt of BExpression * BExpression list * BStmtList
    | BCallStmt of string list * string * BExpression list

type BVarDecl = BVar of string * BType

type BProcedure =
    BProc of string * BVarDecl list * BVarDecl list * BExpression * string list * BExpression * BVarDecl list * BStmtList

type BProgram =
    BProg of string * BProcedure list
