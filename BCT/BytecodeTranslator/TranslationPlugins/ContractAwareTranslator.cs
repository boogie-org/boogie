using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Bpl= Microsoft.Boogie;
using Microsoft.Cci.Contracts;

namespace BytecodeTranslator.TranslationPlugins {
  public abstract class ContractAwareTranslator : Translator {
    public virtual IEnumerable<Bpl.Requires> getPreconditionTranslation(IMethodContract contract) {return new List<Bpl.Requires>(); }
    public virtual IEnumerable<Bpl.Ensures> getPostconditionTranslation(IMethodContract contract) { return new List<Bpl.Ensures>(); }
    public virtual IEnumerable<Bpl.IdentifierExpr> getModifiedIdentifiers(IMethodContract contract) { return new List<Bpl.IdentifierExpr>(); }
  }
}
