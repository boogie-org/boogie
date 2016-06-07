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
    internal BacktrackDictionary<Term, VCExpr> constants_inv = null;
    internal BacktrackDictionary<FuncDecl, Function> functions_inv = null;

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
      {
#if true
          Z3Log.Open(logFilename);
#else
          z3.OpenLog(logFilename);
#endif
      }
      foreach (string tag in debugTraces)
        z3.EnableDebugTrace(tag);

      this.z3log = null;
      this.tm = new Z3TypeCachedBuilder(this);
      this.namer = new UniqueNamer();
    }

    public Z3apiProverContext(Context ctx, VCExpressionGenerator gen)
        : base(gen, new VCGenerationOptions(new List<string>()))
    {
        z3 = ctx;

        this.z3log = null;
        this.tm = new Z3TypeCachedBuilder(this);
        this.namer = new UniqueNamer();

        // For external 

        constants_inv = new BacktrackDictionary<Term, VCExpr>();
        functions_inv = new BacktrackDictionary<FuncDecl, Function>();
    }

    public Term VCExprToTerm(VCExpr expr, LineariserOptions linOptions) {
        Z3apiExprLineariser visitor = new Z3apiExprLineariser(this, namer);
        return (Term)expr.Accept(visitor, linOptions);
    }


    private class fromZ3
    {
        private VCExpressionGenerator gen;
        private Dictionary<Term, VCExpr> memo;
        private BacktrackDictionary<Term, VCExpr> constants_inv;
        private BacktrackDictionary<FuncDecl, Function> functions_inv;
        private List<VCExprLetBinding> lets;
        private int let_ctr = 0;

        private VCExpr create_let(Term t, VCExpr u)
        {
            var name = "$x" + let_ctr.ToString();
            let_ctr++;
            var sym = gen.Variable(name, u.Type);
            memo.Remove(t);
            memo.Add(t, sym);
            lets.Add(gen.LetBinding(sym, u));
            return sym;
        }

        public fromZ3(VCExpressionGenerator _gen,
                      BacktrackDictionary<Term, VCExpr> _constants_inv,
                      BacktrackDictionary<FuncDecl, Function> _functions_inv)
        {
            gen = _gen;
            constants_inv = _constants_inv;
            functions_inv = _functions_inv;
            memo = new Dictionary<Term, VCExpr>();
            lets = new List<VCExprLetBinding>();
        }

        public void clear()
        {
            memo.Clear();
            lets.Clear();
        }
        public VCExpr get(Term arg)
        {
            if (memo.ContainsKey(arg))
                return memo[arg];
            VCExpr res = null;
            switch (arg.GetKind())
            {
                case TermKind.Numeral:
                    var numstr = arg.GetNumeralString();
                    if (arg.GetSort().GetSortKind() == SortKind.Int) {
                      res = gen.Integer(Basetypes.BigNum.FromString(numstr));
                    }
                    else {
                      res = gen.Real(Basetypes.BigDec.FromString(numstr));
                    }
                    break;
                case TermKind.App:
                    var args = arg.GetAppArgs();
                    var vcargs = new VCExpr[args.Length];
                    for (int i = 0; i < args.Length; i++)
                        vcargs[i] = get(args[i]);

                    switch (arg.GetAppDecl().GetKind())
                    {
                        case DeclKind.Add:
                            if (vcargs.Length == 0) {
                              if (arg.GetSort().GetSortKind() == SortKind.Int) {
                                res = gen.Integer(Basetypes.BigNum.ZERO);
                              }
                              else {
                                res = gen.Real(Basetypes.BigDec.ZERO);
                              }
                            }
                            else
                            {
                                res = vcargs[0];
                                for (int k = 1; k < vcargs.Length; k++)
                                    res = gen.Add(res, vcargs[k]);
                            }
                            break;
                        case DeclKind.And:
                            res = VCExpressionGenerator.True;
                            for (int i = 0; i < vcargs.Length; i++)
                                res = gen.AndSimp(res, vcargs[i]);
                            break;
                        case DeclKind.Div:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.RealDivOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Eq:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Eq(vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.False:
                            res = VCExpressionGenerator.False;
                            break;
                        case DeclKind.Ge:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.GeOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Gt:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Gt(vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.IDiv:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.DivOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Iff:
                            Debug.Assert(vcargs.Length == 2);
                            var l = create_let(args[0], vcargs[0]);
                            var r = create_let(args[1], vcargs[1]);
                            return gen.And(gen.Implies(l, r), gen.Implies(r, l));
                        case DeclKind.Implies:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Implies(vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Ite:
                            Debug.Assert(vcargs.Length == 3);
                            res = gen.Function(VCExpressionGenerator.IfThenElseOp, vcargs[0], vcargs[1], vcargs[2]);
                            break;
                        case DeclKind.Le:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.LeOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Lt:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.LtOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Mod:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.ModOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Mul:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.MulOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Not:
                            Debug.Assert(vcargs.Length == 1);
                            res = gen.Not(vcargs[0]);
                            break;
                        case DeclKind.Or:
                            res = VCExpressionGenerator.False;
                            for (int i = 0; i < vcargs.Length; i++)
                                res = gen.OrSimp(res, vcargs[i]);
                            break;
                        case DeclKind.Select:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Select(vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.Store:
                            Debug.Assert(vcargs.Length == 3);
                            res = gen.Store(vcargs[0], vcargs[1], vcargs[2]);
                            break;
                        case DeclKind.Sub:
                            Debug.Assert(vcargs.Length == 2);
                            res = gen.Function(VCExpressionGenerator.SubOp, vcargs[0], vcargs[1]);
                            break;
                        case DeclKind.True:
                            res = VCExpressionGenerator.True;
                            break;
                        case DeclKind.Uminus:
                            Debug.Assert(vcargs.Length == 1);
                            var argzero = null;
                            if (vcargs[0].Type.IsInt) {
                              argzero = gen.Integer(Basetypes.BigNum.ZERO);
                            }
                            else {
                              argzero = gen.Real(Basetypes.BigDec.ZERO);
                            }
                            res = gen.Function(VCExpressionGenerator.SubOp, argzero, vcargs[0]);
                            break;
                        case DeclKind.ToInt:
                            Debug.Assert(vcargs.Length == 1);
                            res = gen.Function(VCExpressionGenerator.ToIntOp, vcargs[0]);
                            break;
                        case DeclKind.ToReal:
                            Debug.Assert(vcargs.Length == 1);
                            res = gen.Function(VCExpressionGenerator.ToRealOp, vcargs[0]);
                            break;
                        case DeclKind.Uninterpreted:
                            var name = arg.GetAppDecl().GetDeclName();
                            if (args.Length == 0)
                            { // a 0-ary constant is a VCExprVar
                                if (!constants_inv.TryGetValue(arg, out res))
                                    throw new Exception("Z3 returned unknown constant: " + name);
                            }
                            else
                            {
                                Function f;
                                if (!functions_inv.TryGetValue(arg.GetAppDecl(), out f))
                                    throw new Exception("Z3 returned unknown function: " + name);
                                List<VCExpr> vcargsList = new List<VCExpr>(vcargs);
                                res = gen.Function(f, vcargsList);
                            }   
                            break;
                        default:
                            throw new Exception("Unknown Z3 operator");
                    }
                    break;
                default:
                    Debug.Assert(false);
                    throw new Exception("Unknown Z3 AST kind");
            }

            memo.Add(arg, res);
            return res;
        }
        public VCExpr add_lets(VCExpr e)
        {
            foreach (var let in lets)
            {
                e = gen.Let(e, let);
            }
            return e;
        }
    }

    public VCExpr TermToVCExpr(Term t)
    {
      var fZ = new fromZ3(gen, constants_inv, functions_inv);
      return fZ.add_lets(fZ.get(t));
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
      if(functions_inv != null)functions_inv.Add(constDeclAst, f);
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
#if true
        Z3Log.Close();
#else
        z3.CloseLog();
#endif
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
      if(constants_inv != null)constants_inv.CreateBacktrackPoint();
      if(functions_inv != null)functions_inv.CreateBacktrackPoint();
      z3.Push();
      log("(push)");
    }

    public void Backtrack() {
      z3.Pop();
      labels.Backtrack();
      functions.Backtrack();
      constants.Backtrack();
      symbols.Backtrack();
      if (constants_inv != null) constants_inv.Backtrack();
      if (functions_inv != null) functions_inv.Backtrack();
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

    public Term GetConstant(string constantName, Type constantType, VCExpr node)
    {
      Term typeSafeTerm;
      if (!constants.ContainsKey(constantName))
        this.DeclareConstant(constantName, constantType);

      if (!constants.TryGetValue(constantName, out typeSafeTerm))
        throw new Exception("constant " + constantName + " is not defined");

      if (constants_inv != null && !constants_inv.ContainsKey(typeSafeTerm))
          constants_inv.Add(typeSafeTerm, node);

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