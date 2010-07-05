using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;

namespace RegressionTestInput {
  public class Class0 {
    void M(int x) {
      int y = (5 / x) + (x = 3);
      Contract.Assert(x == 3 && y <= 8);
    }

    int NonVoid() {
      return 3;
    }

    int OutParam(out int x) {
      x = 3;
      return x;
    }

    int RefParam(ref int x) {
      x = x + 1;
      return x;
    }

    int AssignToInParam(int x) {
      x = x + 1;
      return x;
    }

  }
}
