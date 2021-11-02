// RUN: %parallel-boogie /prune:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Ty;
const unique TBool : Ty;

type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool : TyTag uses {
    axiom Tag(TBool) == TagBool;
}

function Magic<T>(x: T): T uses {
    axiom (forall<T> x: T :: Magic(x) == 3);
}

procedure test() 
  ensures Magic(4) == 3;
  ensures TagBool == Tag(TBool);
{
  
}