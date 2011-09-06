procedure {:barrier} BARRIER(); // Used to mark out barriers in the code; parameter simply lets us label each barrier

type {:thread_id} ThreadId = Pair;

type Pair;

function constructPair(int, int) returns (Pair);
function getX(Pair) returns (int);
function getY(Pair) returns (int);

axiom (forall x, y: int :: {constructPair(y, x)} (getX(constructPair(y, x)) == x) && (getY(constructPair(y, x)) == y));
axiom (forall p: Pair :: {getX(p)} {getY(p)} constructPair(getY(p), getX(p)) == p);

function {:inline} setX(p: Pair, x: int) returns (Pair)
{
    constructPair(getY(p), x)
}

function {:inline} setY(p: Pair, y: int) returns (Pair)
{
    constructPair(y, getX(p))
}

// Thread ids

axiom BLOCK_X == BLOCK_SIZE;
axiom BLOCK_Y == BLOCK_SIZE;
axiom TILE_X == BLOCK_SIZE;
axiom TILE_Y == BLOCK_SIZE;

const BLOCK_X: int;
const TILE_X: int;
const NUM_TILES_X: int;
axiom TILE_X*NUM_TILES_X == BLOCK_X;

const BLOCK_Y: int;
const TILE_Y: int;
const NUM_TILES_Y: int;
axiom TILE_Y*NUM_TILES_Y == BLOCK_Y;

function {:inline} localId(t: ThreadId) returns (Pair)
{
  constructPair( mod(getY(t), TILE_Y ), mod(getX(t), TILE_X) )
}

function {:inline} tileId(t: ThreadId) returns (Pair)
{
  constructPair( div(getY(t), TILE_Y ), div(getX(t), TILE_X) )
}

function {:inline} distinct_same_tile(i: ThreadId, j: ThreadId) returns (bool)
{
  i != j && tileId(i) == tileId(j)
}

function {:builtin "div"} div(int, int) : int;
function {:builtin "mod"} mod(int, int) : int;

// These are the declarations that allow race and divergence checking

var AT_BARRIER : [ThreadId]int;

type ArrayBase;

const unique nothing: ArrayBase;

var base     : [ThreadId]ArrayBase;
var offset_x : [ThreadId]int;
var offset_y : [ThreadId]int;
var offset_z : [ThreadId]int;
var is_write : [ThreadId]bool;

function race(b: [ThreadId]ArrayBase, z: [ThreadId]int, y: [ThreadId]int, x: [ThreadId]int, is_w: [ThreadId]bool, i: ThreadId, j: ThreadId) returns (bool)
{
  (is_w[i] || is_w[j]) && (b[i] != nothing && b[j] != nothing) && (b[i] == b[j]) && (z[i] == z[j]) && (y[i] == y[j]) && (x[i] == x[j])
}

procedure {:inline 1} LOG_READ(b: ArrayBase, z: int, y: int, x: int, i: ThreadId)
modifies base, offset_z, offset_y, offset_x, is_write;
{
  if(*) {
    base[i] := b;
    offset_z[i] := z;
    offset_y[i] := y;
    offset_x[i] := x;
    is_write[i] := false;
  }
}

procedure {:inline 1} LOG_WRITE(b: ArrayBase, z: int, y: int, x: int, i: ThreadId)
modifies base, offset_z, offset_y, offset_x, is_write;
{
  if(*) {
    base[i] := b;
    offset_z[i] := z;
    offset_y[i] := y;
    offset_x[i] := x;
    is_write[i] := true;
  }
}
