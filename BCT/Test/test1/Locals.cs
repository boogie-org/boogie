using System;
using System.Collections.Generic;
//using System.Diagnostics.Contracts;

class Program
{
  private int i;

  void M0(int j) {
    i = 7;
    int k;
    k = i + 20;
    i = k / j;  // error: possible division by zero
  }

  void M1(int j) {
    //    Contract.Requires(0 < j);
    if (!(0 < j)) throw new Exception();
    i = 7;
    int k = i + 20;
    i = k / j;
  }
}
