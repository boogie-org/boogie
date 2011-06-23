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

namespace Microsoft.Boogie.Z3
{
    public class Z3Config
    {
        private Config config = new Config();
        private int counterexamples;
        private string logFilename;
        private List<string> debugTraces = new List<string>();

        public void SetModel(bool enabled)
        {
            config.SetParamValue("MODEL", (enabled ? "true" : "false"));
        }

        public void SetSoftTimeout(string timeout)
        {
            config.SetParamValue("SOFT_TIMEOUT", timeout);
        }

        public void SetTypeCheck(bool enabled)
        {
            config.SetParamValue("TYPE_CHECK", (enabled ? "true" : "false"));
        }

        public void SetCounterExample(int counterexample)
        {
            this.counterexamples = counterexample;
        }

        public void SetLogFilename(string filename)
        {
            this.logFilename = filename;
        }

        public Config Config
        {
            get { return this.config; }
        }
        public int Counterexamples
        {
            get { return this.counterexamples; }
        }
        public string LogFilename
        {
            get { return this.logFilename; }
        }

        public void EnableDebugTrace(string debugTrace)
        {
            this.debugTraces.Add(debugTrace);
        }

        public List<string> DebugTraces
        {
            get { return this.debugTraces; }
        }
    }

    internal class PartitionMap
    {
        private Context ctx;
        private Model model;
        private Dictionary<Term, int> termToPartition = new Dictionary<Term, int>();
        private Dictionary<object, int> valueToPartition = new Dictionary<object, int>();
        private List<Object> partitionToValue = new List<Object>();
        private int partitionCounter = 0;
        public int PartitionCounter { get { return partitionCounter; } }

        public PartitionMap(Context ctx, Model z3Model)
        { 
            this.ctx = ctx;
            this.model = z3Model;
        }

        public int GetPartition(Term value)
        {
            int result;
            if (!termToPartition.TryGetValue(value, out result))
            {
                result = partitionCounter++;
                termToPartition.Add(value, result);
                partitionToValue.Add(null);
                object constant = Evaluate(value);
                valueToPartition.Add(constant, result);
                partitionToValue[result] = constant;
            }
            return result;
        }

        private object Evaluate(Term v)
        {
            Sort s = v.GetSort();
            Sort boolSort = ctx.MkBoolSort();
            Sort intSort = ctx.MkIntSort();
            ArrayValue av;
            
            if (s.Equals(boolSort))
            {
                return ctx.GetBoolValue(v);
            }
            else if (s.Equals(intSort)) {
              int i;
              long il;
              uint u;
              ulong ul;
              if (ctx.TryGetNumeralInt(v, out i)) {
                return BigNum.FromInt(i);
              }
              else if (ctx.TryGetNumeralInt64(v, out il)) {
                return BigNum.FromLong(il);
              }
              else if (ctx.TryGetNumeralUInt(v, out u)) {
                return BigNum.FromUInt(u);
              }
              else if (ctx.TryGetNumeralUInt64(v, out ul)) {
                return BigNum.FromULong(ul);
              }
              else {
                string str = v.ToString();
                return GetPartition(v);
                //return BigNum.FromString(ctx.GetNumeralString(v));
              }
            }
            else if (model.TryGetArrayValue(v, out av)) {
              List<List<int>> arrayValue = new List<List<int>>();
              List<int> tuple;
              for (int i = 0; i < av.Domain.Length; i++) {
                tuple = new List<int>();
                tuple.Add(GetPartition(av.Domain[i]));
                tuple.Add(GetPartition(av.Range[i]));
                arrayValue.Add(tuple);
              }
              tuple = new List<int>();
              tuple.Add(GetPartition(av.ElseCase));
              arrayValue.Add(tuple);
              return arrayValue;
            }
            else {
              // The term is uninterpreted; just return the partition id.
              return GetPartition(v);
            }
        }

        public List<Object> PartitionToValue(Context ctx) 
        {
            return partitionToValue;
        }

        public Dictionary<object, int> ValueToPartition(Context ctx)
        {
            return valueToPartition;
        }
    }

    internal class BacktrackDictionary<K, V>
    {
        private Dictionary<K, V> dictionary = new Dictionary<K, V>();
        private Stack<List<K>> keyStack = new Stack<List<K>>();

        public BacktrackDictionary()
        {
            CreateBacktrackPoint();
        }

        public bool TryGetValue(K key, out V val)
        {
            return dictionary.TryGetValue(key, out val);
        }

        public void Add(K key, V v)
        {
            if (dictionary.ContainsKey(key))
            {
                dictionary.Remove(key);
            }
            dictionary.Add(key, v);
            keyStack.Peek().Add(key);
        }

        public bool ContainsKey(K k)
        {
            return dictionary.ContainsKey(k);
        }

        public void CreateBacktrackPoint()
        {
            keyStack.Push(new List<K>());
        }

        public void Backtrack()
        {
            List<K> keysToErase = keyStack.Pop();
            foreach (K key in keysToErase)
            {
                dictionary.Remove(key);
            }
            if (keyStack.Count == 0)
                this.CreateBacktrackPoint();
        }

        public IEnumerator GetEnumerator()
        {
            return dictionary.Keys.GetEnumerator();
        }
    }

    internal class BoogieErrorModelBuilder
    {
        private Z3Context container;
        private PartitionMap partitionMap;

        public BoogieErrorModelBuilder(Z3Context container, Model z3Model)
        {
            this.container = container;
            this.partitionMap = new PartitionMap(((Z3Context)container).z3, z3Model);
        }
        
        private Dictionary<string, int> CreateConstantToPartition(Model z3Model)
        {
            Dictionary<string, int> constantToPartition = new Dictionary<string, int>();
            foreach (FuncDecl c in z3Model.GetModelConstants())
            {
                string name = container.GetDeclName(c);
                int pid = partitionMap.GetPartition(z3Model.Eval(c, new Term[0]));
                constantToPartition.Add(name, pid);
            }
            return constantToPartition;
        }

        private List<List<string>> CreatePartitionToConstant(Dictionary<string, int> constantToPartition)
        {
            List<List<string>> partitionToConstant = new List<List<string>>();
            for (int i = 0; i < partitionMap.PartitionCounter; i++)
            {
                partitionToConstant.Add(new List<string>());
            }
            foreach (string s in constantToPartition.Keys)
            {
                partitionToConstant[constantToPartition[s]].Add(s);
            }
            return partitionToConstant;
        }

        private Dictionary<string, List<List<int>>> CreateFunctionToPartition(Model z3Model)
        {
            Dictionary<string, List<List<int>>> functionToPartition = new Dictionary<string, List<List<int>>>();

            foreach (KeyValuePair<FuncDecl, FunctionGraph> kv in z3Model.GetFunctionGraphs())
            {
                List<List<int>> f_tuples = new List<List<int>>();
                string f_name = container.GetDeclName(kv.Key);
                FunctionGraph graph = kv.Value;
                foreach (FunctionEntry entry in graph.Entries)
                {
                    List<int> tuple = new List<int>();
                    foreach (Term v in entry.Arguments)
                    {
                        tuple.Add(partitionMap.GetPartition(z3Model.Eval(v)));
                    }
                    tuple.Add(partitionMap.GetPartition(z3Model.Eval(entry.Result)));
                    f_tuples.Add(tuple);
                }
                List<int> else_tuple = new List<int>();
                else_tuple.Add(partitionMap.GetPartition(z3Model.Eval(graph.Else)));
                f_tuples.Add(else_tuple);
                functionToPartition.Add(f_name, f_tuples);
            }
            return functionToPartition;
        }

        public Z3ErrorModel BuildBoogieModel(Model z3Model)
        {
            Dictionary<string, int> constantToPartition = CreateConstantToPartition(z3Model);
            Dictionary<string, List<List<int>>> functionToPartition = CreateFunctionToPartition(z3Model);
            List<List<string>> partitionToConstant = CreatePartitionToConstant(constantToPartition);
            List<Object> partitionToValue = partitionMap.PartitionToValue(((Z3Context)container).z3);
            Dictionary<object, int> valueToPartition = partitionMap.ValueToPartition(((Z3Context)container).z3);
            return new Z3ErrorModel(constantToPartition, partitionToConstant, partitionToValue, valueToPartition, functionToPartition);
        }
    }

    public class Z3ErrorModelAndLabels
    {
        private Z3ErrorModel _errorModel;
        private List<string> _relevantLabels;
        public Z3ErrorModel ErrorModel
        {
            get { return this._errorModel; }
        }
        public List<string> RelevantLabels
        {
            get { return this._relevantLabels; }
        }
        public Z3ErrorModelAndLabels(Z3ErrorModel errorModel, List<string> relevantLabels)
        {
            this._errorModel = errorModel;
            this._relevantLabels = relevantLabels;
        }
    }

    public class Z3Context {
      private BacktrackDictionary<string, Symbol> symbols = new BacktrackDictionary<string, Symbol>();
      internal BacktrackDictionary<string, Term> constants = new BacktrackDictionary<string, Term>();
      internal BacktrackDictionary<string, FuncDecl> functions = new BacktrackDictionary<string, FuncDecl>();
      internal BacktrackDictionary<string, Term> labels = new BacktrackDictionary<string, Term>();

      public Context z3;
      public Z3Config config;
      public Z3apiProverContext ctxt;
      private VCExpressionGenerator gen;
      private Z3TypeCachedBuilder tm;
      private UniqueNamer namer;
      public UniqueNamer Namer {
        get { return namer; }
      }
      private StreamWriter z3log;
      public Z3Context(Z3apiProverContext ctxt, Z3Config config, VCExpressionGenerator gen) {
        Context z3 = new Context(config.Config);
        if (config.LogFilename != null)
          z3.OpenLog(config.LogFilename);
        foreach (string tag in config.DebugTraces)
          z3.EnableDebugTrace(tag);
        this.ctxt = ctxt;
        this.z3 = z3;
        this.config = config;
        this.tm = new Z3TypeCachedBuilder(this);
        this.gen = gen;
        this.namer = new UniqueNamer();
        this.z3.SetPrintMode(PrintMode.Smtlib2Compliant);
        this.z3log = null;
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

      public string GetDeclName(FuncDecl constDeclAst) {
        Symbol symbol = z3.GetDeclName(constDeclAst);
        return z3.GetSymbolString(symbol);
      }

      public Pattern MakePattern(List<Term> exprs) {
        Pattern pattern = z3.MkPattern(exprs.ToArray());
        return pattern;
      }

      private List<Sort> GetTypes(List<Type> boogieTypes) {
        List<Sort> z3Types = new List<Sort>();
        foreach (Type boogieType in boogieTypes) {
          Sort type = tm.GetType(boogieType);
          z3Types.Add(type);
        }
        return z3Types;
      }

      public Term MakeQuantifier(bool isForall, uint weight, string qid, int skolemid, List<string> varNames, List<Type> boogieTypes, List<Pattern> patterns, List<Term> no_patterns, Term body) {
        List<Term> bound = new List<Term>();
        for (int i = 0; i < varNames.Count; i++) {
          Term t = GetConstant(varNames[i], boogieTypes[i]);
          bound.Add(t);
        }

        Term termAst = z3.MkQuantifier(isForall, weight, z3.MkSymbol(qid), z3.MkSymbol(skolemid.ToString()), patterns.ToArray(), no_patterns.ToArray(), bound.ToArray(), body);
        return termAst;
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

      private Z3ErrorModelAndLabels BuildZ3ErrorModel(Model z3Model, List<string> relevantLabels) {
        BoogieErrorModelBuilder boogieErrorBuilder = new BoogieErrorModelBuilder(this, z3Model);
        Z3ErrorModel boogieModel = boogieErrorBuilder.BuildBoogieModel(z3Model);
        return new Z3ErrorModelAndLabels(boogieModel, new List<string>(relevantLabels));
      }

      private void DisplayRelevantLabels(List<string> relevantLabels) {
        foreach (string labelName in relevantLabels) {
          System.Console.Write(labelName + ",");
        }
        System.Console.WriteLine("---");
      }

      public ProverInterface.Outcome Check(out List<Z3ErrorModelAndLabels> boogieErrors) {
        Microsoft.Boogie.Helpers.ExtraTraceInformation("Sending data to the theorem prover");
        boogieErrors = new List<Z3ErrorModelAndLabels>();
        LBool outcome = LBool.Undef;
        Debug.Assert(0 < this.config.Counterexamples);
        while (true) {
          Model z3Model;
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
          boogieErrors.Add(BuildZ3ErrorModel(z3Model, labelStrings));

          if (boogieErrors.Count < this.config.Counterexamples) {
            z3.BlockLiterals(labels);
            log("block-literals {0}", labels);
          }

          labels.Dispose();
          z3Model.Dispose();
          if (boogieErrors.Count == this.config.Counterexamples)
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

        Model z3Model;
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
          boogieErrors.Add(BuildZ3ErrorModel(z3Model, labelStrings));

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

      public void DeclareType(string typeName) {
        log("(declare-sort {0})", typeName);
      }

      public void DeclareConstant(string constantName, Type boogieType) {
        Symbol symbolAst = GetSymbol(constantName);
        Sort typeAst = tm.GetType(boogieType);

        Term constAst = z3.MkConst(symbolAst, typeAst);
        constants.Add(constantName, constAst);
        log("(declare-funs (({0} {1})))", constAst, typeAst);
      }

      public void DeclareFunction(string functionName, List<Type> domain, Type range) {
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

      private List<Symbol> GetSymbols(List<string> symbolNames) {
        List<Symbol> symbols = new List<Symbol>();
        foreach (string symbolName in symbolNames)
          symbols.Add(GetSymbol(symbolName));
        return symbols;
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

      private FuncDecl GetFunction(string functionName) {
        FuncDecl function;
        if (!functions.TryGetValue(functionName, out function))
          throw new Exception("function " + functionName + " is undefined");
        return function;
      }

      public Term GetConstant(string constantName, Type constantType) {
        Term typeSafeTerm;
        if (!constants.ContainsKey(constantName))
          this.DeclareConstant(constantName, constantType);

        if (!constants.TryGetValue(constantName, out typeSafeTerm))
          throw new Exception("constant " + constantName + " is not defined");
        return typeSafeTerm;
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

      public Term Make(string op, List<Term> children) {
        Term[] unwrapChildren = children.ToArray();
        Term term;
        switch (op) {
          // formulas  
          case "AND": term = z3.MkAnd(unwrapChildren); break;
          case "OR": term = z3.MkOr(unwrapChildren); break;
          case "IMPLIES": term = z3.MkImplies(unwrapChildren[0], unwrapChildren[1]); break;
          case "NOT": term = z3.MkNot(unwrapChildren[0]); break;
          case "IFF": term = z3.MkIff(unwrapChildren[0], unwrapChildren[1]); break;
          // terms
          case "EQ": term = z3.MkEq(unwrapChildren[0], unwrapChildren[1]); break;
          case "NEQ": term = z3.MkNot(z3.MkEq(unwrapChildren[0], unwrapChildren[1])); break;
          case "DISTINCT": term = z3.MkDistinct(unwrapChildren); break;
          // terms
          case "<": term = z3.MkLt(unwrapChildren[0], unwrapChildren[1]); break;
          case ">": term = z3.MkGt(unwrapChildren[0], unwrapChildren[1]); break;
          case "<=": term = z3.MkLe(unwrapChildren[0], unwrapChildren[1]); break;
          case ">=": term = z3.MkGe(unwrapChildren[0], unwrapChildren[1]); break;
          case "+": term = z3.MkAdd(unwrapChildren); break;
          case "-": term = z3.MkSub(unwrapChildren); break;
          case "/": term = z3.MkDiv(unwrapChildren[0], unwrapChildren[1]); break;
          case "%": term = z3.MkMod(unwrapChildren[0], unwrapChildren[1]); break;
          case "*": term = z3.MkMul(unwrapChildren); break;
          default: {
              FuncDecl f = GetFunction(op);
              term = z3.MkApp(f, unwrapChildren);
            }
            break;
        }
        return term;
      }
    }
}