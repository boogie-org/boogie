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
using Microsoft.Basetypes;

using Z3Model = Microsoft.Z3.Model;
using BoogieModel = Microsoft.Boogie.Model;

namespace Microsoft.Boogie.Z3 {
  public class Z3apiProverContext : DeclFreeProverContext {
    private BacktrackDictionary<string, Symbol> symbols = new BacktrackDictionary<string, Symbol>();
    internal BacktrackDictionary<string, Term> constants = new BacktrackDictionary<string, Term>();
    internal BacktrackDictionary<string, FuncDecl> functions = new BacktrackDictionary<string, FuncDecl>();
    internal BacktrackDictionary<string, Term> labels = new BacktrackDictionary<string, Term>();

    public Config config;
    public Context z3;

    private Z3TypeCachedBuilder tm;
    private UniqueNamer namer;
    private StreamWriter z3log;

    private int counterexamples;
    private string logFilename;
    private List<string> debugTraces;

    public Z3apiProverContext(Z3InstanceOptions opts, VCExpressionGenerator gen)
      : base(gen, new VCGenerationOptions(new List<string>())) {
      int timeout = opts.Timeout * 1000;
      config = new Config();
      config.SetParamValue("MODEL", "true");
      config.SetParamValue("MODEL_V2", "true");
      config.SetParamValue("MODEL_COMPLETION", "true");
      config.SetParamValue("MBQI", "false");
      config.SetParamValue("TYPE_CHECK", "true");
      if (0 <= timeout) {
        config.SetParamValue("SOFT_TIMEOUT", timeout.ToString());
      }

      if (0 <= CommandLineOptions.Clo.ProverCCLimit) {
        this.counterexamples = CommandLineOptions.Clo.ProverCCLimit;
      }
      if (CommandLineOptions.Clo.SimplifyLogFilePath != null) {
        logFilename = CommandLineOptions.Clo.SimplifyLogFilePath;
      }
      this.debugTraces = new List<string>();

      z3 = new Context(config);
      z3.SetPrintMode(PrintMode.Smtlib2Compliant);
      if (logFilename != null)
        z3.OpenLog(logFilename);
      foreach (string tag in debugTraces)
        z3.EnableDebugTrace(tag);

      this.z3log = null;
      this.tm = new Z3TypeCachedBuilder(this);
      this.namer = new UniqueNamer();
    }

    public override void DeclareType(TypeCtorDecl t, string attributes) {
      base.DeclareType(t, attributes);
      log("(declare-sort {0})", t.Name);
    }

    public override void DeclareConstant(Constant c, bool uniq, string attributes) {
      base.DeclareConstant(c, uniq, attributes);
      DeclareConstant(c.Name, c.TypedIdent.Type);
    }

    public override void DeclareFunction(Function f, string attributes) {
      base.DeclareFunction(f, attributes);
      List<Type> domain = new List<Type>();
      foreach (Variable v in f.InParams) {
        domain.Add(v.TypedIdent.Type);
      }
      if (f.OutParams.Length != 1)
        throw new Exception("Cannot handle functions with " + f.OutParams + " out parameters.");
      Type range = f.OutParams[0].TypedIdent.Type;

      string functionName = f.Name;
      Symbol symbolAst = GetSymbol(functionName);
      var domainStr = "";
      List<Sort> domainAst = new List<Sort>();
      foreach (Type domainType in domain) {
        Sort type = tm.GetType(domainType);
        domainAst.Add(type);
        domainStr += type.ToString() + " ";
      }
      Sort rangeAst = tm.GetType(range);
      FuncDecl constDeclAst = z3.MkFuncDecl(symbolAst, domainAst.ToArray(), rangeAst);
      functions.Add(functionName, constDeclAst);
      log("(declare-funs (({0} {1} {2})))", functionName, domainStr, rangeAst);
    }

    public override void DeclareGlobalVariable(GlobalVariable v, string attributes) {
      base.DeclareGlobalVariable(v, attributes);
      DeclareConstant(v.Name, v.TypedIdent.Type);
    }

    public override string Lookup(VCExprVar var) {
      return namer.Lookup(var);
    }

    public void log(string format, params object[] args) {
      // Currently, this is a no-op because z3log is always null
      // We use the default (automatic) tracing facility of z3
      if (z3log != null) {
        var str = string.Format(format, args);
        // Do standard string replacement
        str = str.Replace("array", "Array");
        z3log.WriteLine(str);
        z3log.Flush();
      }
    }

    public void CloseLog() {
      z3.CloseLog();
      if (z3log != null) {
        z3log.Close();
      }
      z3log = null;
    }

    public void CreateBacktrackPoint() {
      symbols.CreateBacktrackPoint();
      constants.CreateBacktrackPoint();
      functions.CreateBacktrackPoint();
      labels.CreateBacktrackPoint();
      z3.Push();
      log("(push)");
    }

    public void Backtrack() {
      z3.Pop();
      labels.Backtrack();
      functions.Backtrack();
      constants.Backtrack();
      symbols.Backtrack();
      log("(pop)");
    }

    public void AddAxiom(VCExpr axiom, LineariserOptions linOptions) {
      Z3apiExprLineariser visitor = new Z3apiExprLineariser(this, namer);
      Term term = (Term)axiom.Accept(visitor, linOptions);
      log("(assert {0})", term);
      z3.AssertCnstr(term);
    }

    public void AddConjecture(VCExpr vc, LineariserOptions linOptions) {
      VCExpr not_vc = (VCExpr)this.gen.Not(vc);
      Z3apiExprLineariser visitor = new Z3apiExprLineariser(this, namer);
      Term term = (Term)not_vc.Accept(visitor, linOptions);
      log("(assert {0})", term);
      z3.AssertCnstr(term);
    }

    public void AddSmtlibString(string smtlibString) {
      FuncDecl[] decls;
      Term[] assumptions;
      Term[] terms;
      Sort[] sorts;
      string tmp;

      z3.ParseSmtlibString(smtlibString, new Sort[] { }, new FuncDecl[] { },
                           out assumptions, out terms, out decls, out sorts, out tmp);
      // TBD: check with Nikolaj about the correct position of assumptions
      foreach (FuncDecl decl in decls) {
        Symbol symbol = z3.GetDeclName(decl);
        string functionName = z3.GetSymbolString(symbol);
        functions.Add(functionName, decl);
      }
      foreach (Term assumption in assumptions) {
        log("(assert {0})", assumption);
        z3.AssertCnstr(assumption);
      }
    }

    private List<Sort> GetTypes(List<Type> boogieTypes) {
      List<Sort> z3Types = new List<Sort>();
      foreach (Type boogieType in boogieTypes) {
        Sort type = tm.GetType(boogieType);
        z3Types.Add(type);
      }
      return z3Types;
    }

    private static bool Equals(List<string> l, List<string> r) {
      Debug.Assert(l != null);
      if (r == null)
        return false;

      if (l.Count != r.Count)
        return false;

      for (int i = 0; i < l.Count; i++)
        if (!l[i].Equals(r[i]))
          return false;
      return true;
    }

    private void DisplayRelevantLabels(List<string> relevantLabels) {
      foreach (string labelName in relevantLabels) {
        System.Console.Write(labelName + ",");
      }
      System.Console.WriteLine("---");
    }

    private void DeclareConstant(string constantName, Type boogieType) {
      Symbol symbolAst = GetSymbol(constantName);
      Sort typeAst = tm.GetType(boogieType);

      Term constAst = z3.MkConst(symbolAst, typeAst);
      constants.Add(constantName, constAst);
      log("(declare-funs (({0} {1})))", constAst, typeAst);
    }

    public ProverInterface.Outcome Check(out List<Z3ErrorModelAndLabels> boogieErrors) {
      Microsoft.Boogie.Helpers.ExtraTraceInformation("Sending data to the theorem prover");
      boogieErrors = new List<Z3ErrorModelAndLabels>();
      LBool outcome = LBool.Undef;
      Debug.Assert(0 < this.counterexamples);
      while (true) {
        Z3Model z3Model;
        outcome = z3.CheckAndGetModel(out z3Model);

        log("(check-sat)");
        if (outcome == LBool.False)
          break;

        if (outcome == LBool.Undef && z3Model == null) {
          // Blame this on timeout
          return ProverInterface.Outcome.TimeOut;
        }

        Debug.Assert(z3Model != null);
        LabeledLiterals labels = z3.GetRelevantLabels();
        Debug.Assert(labels != null);

        List<string> labelStrings = new List<string>();
        uint numLabels = labels.GetNumLabels();
        for (uint i = 0; i < numLabels; ++i) {
          Symbol sym = labels.GetLabel(i);
          string labelName = z3.GetSymbolString(sym);
          if (!labelName.StartsWith("@")) {
            labels.Disable(i);
          }
          labelStrings.Add(labelName);
        }

        var sw = new StringWriter();
        sw.WriteLine("*** MODEL");
        z3Model.Display(sw);
        sw.WriteLine("*** END_MODEL");
        var sr = new StringReader(sw.ToString());
        var models = Microsoft.Boogie.Model.ParseModels(sr);
        Z3ErrorModelAndLabels e = new Z3ErrorModelAndLabels(models[0], new List<string>(labelStrings));
        boogieErrors.Add(e);

        if (boogieErrors.Count < this.counterexamples) {
          z3.BlockLiterals(labels);
          log("block-literals {0}", labels);
        }

        labels.Dispose();
        z3Model.Dispose();
        if (boogieErrors.Count == this.counterexamples)
          break;
      }

      if (boogieErrors.Count > 0) {
        return ProverInterface.Outcome.Invalid;
      }
      else if (outcome == LBool.False) {
        return ProverInterface.Outcome.Valid;
      }
      else {
        Debug.Assert(outcome == LBool.Undef);
        return ProverInterface.Outcome.Undetermined;
      }
    }

    public ProverInterface.Outcome CheckAssumptions(List<VCExpr> assumptions, LineariserOptions linOptions,
        out List<Z3ErrorModelAndLabels> boogieErrors,
        out List<int> unsatCore) {
      Microsoft.Boogie.Helpers.ExtraTraceInformation("Sending data to the theorem prover");
      boogieErrors = new List<Z3ErrorModelAndLabels>();
      unsatCore = new List<int>();
      LBool outcome = LBool.Undef;

      Z3Model z3Model;
      Term proof;
      Term[] core;
      Term[] assumption_terms = new Term[assumptions.Count];
      var logstring = "";
      for (int i = 0; i < assumptions.Count; i++) {
        Z3apiExprLineariser visitor = new Z3apiExprLineariser(this, namer);
        Term z3ast = (Term)assumptions[i].Accept(visitor, linOptions);
        assumption_terms[i] = z3ast;
        logstring += string.Format("({0}) ", assumption_terms[i]);
      }

      log("(get-core {0})", logstring);
      outcome = z3.CheckAssumptions(out z3Model, assumption_terms, out proof, out core);

      if (outcome != LBool.False) {
        Debug.Assert(z3Model != null);
        LabeledLiterals labels = z3.GetRelevantLabels();
        Debug.Assert(labels != null);

        List<string> labelStrings = new List<string>();
        uint numLabels = labels.GetNumLabels();
        for (uint i = 0; i < numLabels; ++i) {
          Symbol sym = labels.GetLabel(i);
          string labelName = z3.GetSymbolString(sym);
          if (!labelName.StartsWith("@")) {
            labels.Disable(i);
          }
          labelStrings.Add(labelName);
        }

        var sw = new StringWriter();
        sw.WriteLine("*** MODEL");
        z3Model.Display(sw);
        sw.WriteLine("*** END_MODEL");
        var sr = new StringReader(sw.ToString());
        var models = Microsoft.Boogie.Model.ParseModels(sr);
        Z3ErrorModelAndLabels e = new Z3ErrorModelAndLabels(models[0], new List<string>(labelStrings));
        boogieErrors.Add(e);

        labels.Dispose();
        z3Model.Dispose();
      }

      if (boogieErrors.Count > 0) {
        return ProverInterface.Outcome.Invalid;
      }
      else if (outcome == LBool.False) {
        foreach (Term t in core) {
          for (int i = 0; i < assumption_terms.Length; i++) {
            if (t.Equals(assumption_terms[i]))
              unsatCore.Add(i);
          }
        }
        return ProverInterface.Outcome.Valid;
      }
      else {
        Debug.Assert(outcome == LBool.Undef);
        return ProverInterface.Outcome.Undetermined;
      }
    }

    private Symbol GetSymbol(string symbolName) {
      if (!symbols.ContainsKey(symbolName)) {
        Symbol symbolAst = z3.MkSymbol(symbolName);
        symbols.Add(symbolName, symbolAst);
      }
      Symbol result;
      if (!symbols.TryGetValue(symbolName, out result))
        throw new Exception("symbol " + symbolName + " is undefined");
      return result;
    }

    public Term GetConstant(string constantName, Type constantType) {
      Term typeSafeTerm;
      if (!constants.ContainsKey(constantName))
        this.DeclareConstant(constantName, constantType);

      if (!constants.TryGetValue(constantName, out typeSafeTerm))
        throw new Exception("constant " + constantName + " is not defined");
      return typeSafeTerm;
    }

    public FuncDecl GetFunction(string functionName) {
      FuncDecl f;
      if (!functions.TryGetValue(functionName, out f))
        throw new Exception("function " + functionName + " is undefined");
      return f;
    }

    public Term MakeLabel(string labelName, bool pos, Term child) {
      Symbol labelSymbol = this.GetSymbol(labelName);
      Term labeledExpr = z3.MkLabel(labelSymbol, pos, child);
      labels.Add(labelName, labeledExpr);
      return labeledExpr;
    }

    public LabeledLiterals GetRelevantLabels() {
      LabeledLiterals safeLiterals = z3.GetRelevantLabels();
      log("get-relevant-labels");
      return safeLiterals;
    }
  }

  internal class BacktrackDictionary<K, V> {
    private Dictionary<K, V> dictionary = new Dictionary<K, V>();
    private Stack<List<K>> keyStack = new Stack<List<K>>();

    public BacktrackDictionary() {
      CreateBacktrackPoint();
    }

    public bool TryGetValue(K key, out V val) {
      return dictionary.TryGetValue(key, out val);
    }

    public void Add(K key, V v) {
      if (dictionary.ContainsKey(key)) {
        dictionary.Remove(key);
      }
      dictionary.Add(key, v);
      keyStack.Peek().Add(key);
    }

    public bool ContainsKey(K k) {
      return dictionary.ContainsKey(k);
    }

    public void CreateBacktrackPoint() {
      keyStack.Push(new List<K>());
    }

    public void Backtrack() {
      List<K> keysToErase = keyStack.Pop();
      foreach (K key in keysToErase) {
        dictionary.Remove(key);
      }
      if (keyStack.Count == 0)
        this.CreateBacktrackPoint();
    }

    public IEnumerator GetEnumerator() {
      return dictionary.Keys.GetEnumerator();
    }
  }

  public class Z3ErrorModelAndLabels {
    private Model _model;
    private List<string> _relevantLabels;
    public Model Model {
      get { return this._model; }
    }
    public List<string> RelevantLabels {
      get { return this._relevantLabels; }
    }
    public Z3ErrorModelAndLabels(Model model, List<string> relevantLabels) {
      this._model = model;
      this._relevantLabels = relevantLabels;
    }
  }



}