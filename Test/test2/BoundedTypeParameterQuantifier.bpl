// RUN: %boogie /proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Map#Domain<QUN, YAN>(Map QUN YAN): [QUN] bool;
function Map#Empty<QUN, YAN>(): Map QUN YAN;
type Map QUN YAN;

axiom (forall<QUN, YAN> u: QUN ::
        { Map#Domain(Map#Empty(): Map QUN YAN)[u] }
        !Map#Domain(Map#Empty(): Map QUN YAN)[u]);

procedure P()
{
}
