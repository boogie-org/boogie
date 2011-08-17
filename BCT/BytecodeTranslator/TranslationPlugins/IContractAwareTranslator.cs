using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Bpl= Microsoft.Boogie;
using Microsoft.Cci.Contracts;

namespace BytecodeTranslator.TranslationPlugins {
  interface IContractAwareTranslator : ITranslator {
    IEnumerable<Bpl.Expr> getPreconditionTranslation(IMethodContract contract);
    IEnumerable<Bpl.Expr> getPostconditionTranslation(IMethodContract contract);
    IEnumerable<Bpl.IdentifierExpr> getModifiedIdentifiers(IMethodContract contract);
  }
}
