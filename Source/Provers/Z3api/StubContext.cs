using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Diagnostics;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.Z3;
using Microsoft.Z3;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.Z3 {
  public class Z3StubContext : Z3Context {
    class Z3StubPatternAst: Z3PatternAst {}
    class Z3StubTermAst: Z3TermAst {}
    class Z3StubLabeledLiterals: Z3LabeledLiterals {}
  
    public void CreateBacktrackPoint(){}
    public void Backtrack(){}
    public void AddAxiom(VCExpr axiom, LineariserOptions linOptions) { }
    public void AddConjecture(VCExpr vc, LineariserOptions linOptions){}
    public void AddSmtlibString(string smtlibString) {}
    public string GetDeclName(Z3ConstDeclAst constDeclAst) {
      return "";
    }
    public Z3PatternAst MakePattern(List<Z3TermAst> exprs) {
      return new Z3StubPatternAst();
    }
    public Z3TermAst MakeQuantifier(bool isForall, uint weight, string qid, int skolemid, List<string> varNames, List<Type> boogieTypes, List<Z3PatternAst> patterns, List<Z3TermAst> no_patterns, Z3TermAst body) {
        return new Z3StubTermAst();
    }
    public ProverInterface.Outcome Check(out List<Z3ErrorModelAndLabels> boogieErrors) {
      boogieErrors = new List<Z3ErrorModelAndLabels>();
      return ProverInterface.Outcome.Undetermined;
    }
    public void TypeCheckBool(Z3TermAst t){}
    public void TypeCheckInt(Z3TermAst t){}
    public void DeclareType(string typeName) {}
    public void DeclareConstant(string constantName, Type boogieType) {}
    public void DeclareFunction(string functionName, List<Type> domain, Type range) {}
    public Z3TermAst GetConstant(string constantName, Type constantType) {
      return new Z3StubTermAst();
    }    
    public Z3TermAst MakeIntLiteral(string numeral) {
      return new Z3StubTermAst();
    }
    public Z3TermAst MakeBvLiteral(int i, uint bvSize) {
      return new Z3StubTermAst();
    }
    public Z3TermAst MakeTrue() {
      return new Z3StubTermAst();
    }
    public Z3TermAst MakeFalse() {
      return new Z3StubTermAst();
    }
    public Z3TermAst MakeLabel(string labelName, bool pos, Z3TermAst child) {
      return new Z3StubTermAst();
    }
    public Z3LabeledLiterals GetRelevantLabels() {
      return new Z3StubLabeledLiterals();
    }
    public Z3TermAst Make(string op, List<Z3TermAst> children) {
      return new Z3StubTermAst();
    }
    public Z3TermAst MakeArraySelect(List<Z3TermAst> args)
    {
        return new Z3StubTermAst();
    }
    public Z3TermAst MakeArrayStore(List<Z3TermAst> args)
    {
        return new Z3StubTermAst();
    }
  }
}