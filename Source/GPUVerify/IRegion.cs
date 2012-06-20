using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;

namespace GPUVerify {

interface IRegion {
  object Identifier();
  IEnumerable<Cmd> Cmds();
  IEnumerable<object> CmdsChildRegions();
  IEnumerable<IRegion> SubRegions();
  Expr Guard();
  void AddInvariant(PredicateCmd pc);
}

}
