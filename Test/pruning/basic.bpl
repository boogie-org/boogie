// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ty;
const unique TBool : Ty;

type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool : TyTag uses {
    axiom Tag(TBool) == TagBool;
}

type Box;
function $Box<T>(T): Box;

function {:identity} Lit<T>(x: T): T { x } uses {
    axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );
}