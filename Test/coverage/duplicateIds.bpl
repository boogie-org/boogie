// RUN: %boogie /warnVacuousProofs /trace "%s" > "%t"
// RUN: %OutputCheck "%s" --file-to-check="%t"
// CHECK:Proof dependencies:
// CHECK:  id_l12_c5_assert_0
// CHECK:  id_l12_c5_assert_1
// CHECK:Proof dependencies of whole program:
// CHECK:  id_l12_c5_assert_0
// CHECK:  id_l12_c5_assert_1
procedure P(x: int) {
    assume {:id "id_l12_c5_assert_0"} x > 0;
    assert x > 0;
}
