// RUN: %boogie -proverWarnings:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
type float64 = float53e11;

function {:builtin "(_ fp.to_sbv 64)"} D2I(rmode, float64) returns (bv64);
function {:builtin "(_ to_fp 11 53)"} R2D(rmode, real) returns (float64);

procedure Main()
{
  var rm: rmode;

  rm := RNE;
  assert D2I(rm,R2D(RNE,2.3)) == 2bv64;
  assert D2I(rm,R2D(RNE,2.5)) == 2bv64;
  assert D2I(rm,R2D(RNE,3.5)) == 4bv64;
  assert D2I(rm,R2D(RNE,-2.3)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-2.5)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-3.5)) == 18446744073709551612bv64;

  rm := RTN;
  assert D2I(rm,R2D(RNE,2.3)) == 2bv64;
  assert D2I(rm,R2D(RNE,2.5)) == 2bv64;
  assert D2I(rm,R2D(RNE,3.5)) == 3bv64;
  assert D2I(rm,R2D(RNE,-2.3)) == 18446744073709551613bv64;
  assert D2I(rm,R2D(RNE,-2.5)) == 18446744073709551613bv64;
  assert D2I(rm,R2D(RNE,-3.5)) == 18446744073709551612bv64;

  rm := RNA;
  assert D2I(rm,R2D(RNE,2.3)) == 2bv64;
  assert D2I(rm,R2D(RNE,2.5)) == 3bv64;
  assert D2I(rm,R2D(RNE,-2.3)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-2.5)) == 18446744073709551613bv64;

  // These assertions should pass.
  // They were broken in a previous version of Z3 (4.5.0),
  // but work correctly with Z3 4.8.4.
  assert D2I(rm,R2D(RNE,3.5)) == 4bv64;
  assert D2I(rm,R2D(RNE,-3.5)) == 18446744073709551612bv64;

  rm := RTP;
  assert D2I(rm,R2D(RNE,2.3)) == 3bv64;
  assert D2I(rm,R2D(RNE,2.5)) == 3bv64;
  assert D2I(rm,R2D(RNE,3.5)) == 4bv64;
  assert D2I(rm,R2D(RNE,-2.3)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-2.5)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-3.5)) == 18446744073709551613bv64;

  rm := RTZ;
  assert D2I(rm,R2D(RNE,2.3)) == 2bv64;
  assert D2I(rm,R2D(RNE,2.5)) == 2bv64;
  assert D2I(rm,R2D(RNE,3.5)) == 3bv64;
  assert D2I(rm,R2D(RNE,-2.3)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-2.5)) == 18446744073709551614bv64;
  assert D2I(rm,R2D(RNE,-3.5)) == 18446744073709551613bv64;
}
