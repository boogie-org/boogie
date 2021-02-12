using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.TypeErasure;
using System.Text;
using System.Numerics;

namespace Microsoft.Boogie.SMTLib
{
  public class FunctionDependencyCollector : BoundVarTraversingVCExprVisitor<bool, bool>
  {
    private List<Function> functionList;

    // not used but required by interface
    protected override bool StandardResult(VCExpr node, bool arg)
    {
      return true;
    }

    public List<Function> Collect(VCExpr expr)
    {
      functionList = new List<Function>();
      Traverse(expr, true);
      return functionList;
    }

    public override bool Visit(VCExprNAry node, bool arg)
    {
      VCExprBoogieFunctionOp op = node.Op as VCExprBoogieFunctionOp;
      if (op != null)
      {
        functionList.Add(op.Func);
      }

      return base.Visit(node, arg);
    }
  }

  public class SMTLibProcessTheoremProver : ProverInterface
  {
    private readonly SMTLibProverContext ctx;
    private VCExpressionGenerator gen;
    protected readonly SMTLibProverOptions options;
    private bool usingUnsatCore;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(ctx != null);
      Contract.Invariant(Namer != null);
      Contract.Invariant(DeclCollector != null);
      Contract.Invariant(cce.NonNullElements(Axioms));
      Contract.Invariant(cce.NonNullElements(TypeDecls));
      Contract.Invariant(_backgroundPredicates != null);
    }


    [NotDelayed]
    public SMTLibProcessTheoremProver(ProverOptions options, VCExpressionGenerator gen,
      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);

      InitializeGlobalInformation();

      this.options = (SMTLibProverOptions) options;
      this.ctx = ctx;
      this.gen = gen;
      this.usingUnsatCore = false;

      SetupAxiomBuilder(gen);

      Namer = new SMTLibNamer();
      ctx.parent = this;
      this.DeclCollector = new TypeDeclCollector((SMTLibProverOptions) options, Namer);

      SetupProcess();

      if (CommandLineOptions.Clo.StratifiedInlining > 0 || CommandLineOptions.Clo.ContractInfer)
      {
        // Prepare for ApiChecker usage
        if (options.LogFilename != null && currentLogFile == null)
        {
          currentLogFile = OpenOutputFile("");
        }

        PrepareCommon();
      }
    }

    public override void AssertNamed(VCExpr vc, bool polarity, string name)
    {
      string vcString;
      if (polarity)
      {
        vcString = VCExpr2String(vc, 1);
      }
      else
      {
        vcString = "(not " + VCExpr2String(vc, 1) + ")";
      }

      AssertAxioms();
      SendThisVC(string.Format("(assert (! {0} :named {1}))", vcString, name));
    }

    private void SetupAxiomBuilder(VCExpressionGenerator gen)
    {
      switch (CommandLineOptions.Clo.TypeEncodingMethod)
      {
        case CommandLineOptions.TypeEncoding.Arguments:
          AxBuilder = new TypeAxiomBuilderArguments(gen);
          AxBuilder.Setup();
          break;
        case CommandLineOptions.TypeEncoding.Monomorphic:
          AxBuilder = null;
          break;
        default:
          AxBuilder = new TypeAxiomBuilderPremisses(gen);
          AxBuilder.Setup();
          break;
      }
    }

    void SetupProcess()
    {
      if (Process != null) return;

      Process = new SMTLibProcess(this.options);
      Process.ErrorHandler += this.HandleProverError;
    }


    void PossiblyRestart()
    {
      if (Process != null && Process.NeedsRestart)
      {
        Process.Close();
        Process = null;
        SetupProcess();
        Process.Send(common.ToString());
      }
    }

    public override ProverContext Context
    {
      get
      {
        Contract.Ensures(Contract.Result<ProverContext>() != null);

        return ctx;
      }
    }

    internal TypeAxiomBuilder AxBuilder { get; private set; }
    private TypeAxiomBuilder CachedAxBuilder;
    private UniqueNamer CachedNamer;
    internal UniqueNamer Namer { get; private set; }
    readonly TypeDeclCollector DeclCollector;
    protected SMTLibProcess Process;
    readonly List<string> proverErrors = new List<string>();
    readonly List<string> proverWarnings = new List<string>();
    StringBuilder common = new StringBuilder();
    private string CachedCommon = null;
    protected TextWriter currentLogFile;
    protected volatile ErrorHandler currentErrorHandler;

    private void FeedTypeDeclsToProver()
    {
      foreach (string s in DeclCollector.GetNewDeclarations())
      {
        Contract.Assert(s != null);
        AddTypeDecl(s);
      }
    }

    private string Sanitize(string msg)
    {
      var idx = msg.IndexOf('\n');
      if (idx > 0)
        msg = msg.Replace("\r", "").Replace("\n", "\r\n");
      return msg;
    }

    public override void LogComment(string comment)
    {
      SendCommon("; " + comment);
    }

    private void SendCommon(string s)
    {
      Send(s, true);
    }

    protected void SendThisVC(string s)
    {
      Send(s, false);
    }

    private void Send(string s, bool isCommon)
    {
      s = Sanitize(s);

      if (isCommon)
        common.Append(s).Append("\r\n");

      if (Process != null)
        Process.Send(s);
      if (currentLogFile != null)
      {
        currentLogFile.WriteLine(s);
        currentLogFile.Flush();
      }
    }

    private void FindDependentTypes(Type type, List<DatatypeTypeCtorDecl> dependentTypes)
    {
      MapType mapType = type as MapType;
      if (mapType != null)
      {
        foreach (Type t in mapType.Arguments)
        {
          FindDependentTypes(t, dependentTypes);
        }

        FindDependentTypes(mapType.Result, dependentTypes);
      }

      CtorType ctorType = type as CtorType;
      if (ctorType != null && ctorType.Decl is DatatypeTypeCtorDecl datatypeTypeCtorDecl && ctx.KnownDatatypes.Contains(datatypeTypeCtorDecl))
      {
        dependentTypes.Add(datatypeTypeCtorDecl);
      }
    }

    private void PrepareDataTypes()
    {
      if (ctx.KnownDatatypes.Count > 0)
      {
        GraphUtil.Graph<DatatypeTypeCtorDecl> dependencyGraph = new GraphUtil.Graph<DatatypeTypeCtorDecl>();
        foreach (var datatype in ctx.KnownDatatypes)
        {
          dependencyGraph.AddSource(datatype);
          // Check for user-specified dependency (using ":dependson" attribute).
          string userDependency = datatype.GetTypeDependency();
          if (userDependency != null)
          {
            dependencyGraph.AddEdge(datatype, ctx.LookupDatatype(userDependency));
          }

          foreach (Function f in datatype.Constructors)
          {
            var dependentTypes = new List<DatatypeTypeCtorDecl>();
            foreach (Variable v in f.InParams)
            {
              FindDependentTypes(v.TypedIdent.Type, dependentTypes);
            }
            foreach (var result in dependentTypes)
            {
              dependencyGraph.AddEdge(datatype, result);
            }
          }
        }

        GraphUtil.StronglyConnectedComponents<DatatypeTypeCtorDecl> sccs =
          new GraphUtil.StronglyConnectedComponents<DatatypeTypeCtorDecl>(dependencyGraph.Nodes, dependencyGraph.Predecessors,
            dependencyGraph.Successors);
        sccs.Compute();
        foreach (GraphUtil.SCC<DatatypeTypeCtorDecl> scc in sccs)
        {
          string datatypesString = "";
          string datatypeConstructorsString = "";
          foreach (var datatype in scc)
          {
            datatypesString += "(" + SMTLibExprLineariser.TypeToString(new CtorType(Token.NoToken, datatype, new List<Type>())) + " 0)";
            string datatypeConstructorString = "";
            foreach (Function f in datatype.Constructors)
            {
              string quotedConstructorName = Namer.GetQuotedName(f, f.Name);
              datatypeConstructorString += "(" + quotedConstructorName + " ";
              foreach (Variable v in f.InParams)
              {
                string quotedSelectorName = Namer.GetQuotedName(v, v.Name + "#" + f.Name);
                datatypeConstructorString += "(" + quotedSelectorName + " " +
                                             DeclCollector.TypeToStringReg(v.TypedIdent.Type) + ") ";
              }

              datatypeConstructorString += ") ";
            }

            datatypeConstructorsString += "(" + datatypeConstructorString + ") ";
          }

          List<string> decls = DeclCollector.GetNewDeclarations();
          foreach (string decl in decls)
          {
            SendCommon(decl);
          }

          SendCommon("(declare-datatypes (" + datatypesString + ") (" + datatypeConstructorsString + "))");
        }
      }
    }

    private void PrepareFunctionDefinitions()
    {
      // Collect all function definitions to be processed
      Stack<Function> functionDefs = new Stack<Function>();
      foreach (Function f in ctx.DefinedFunctions.Keys)
      {
        DeclCollector.AddKnownFunction(f); // add func to knows funcs so that it does not get declared later on
        functionDefs.Push(f);
      }

      // Process each definition, but also be sure to process dependencies first in case one
      // definition calls another.
      // Also check for definition cycles.
      List<string> generatedFuncDefs = new List<string>();
      FunctionDependencyCollector collector = new FunctionDependencyCollector();
      HashSet<Function> definitionAdded = new HashSet<Function>(); // whether definition has been fully processed
      HashSet<Function>
        dependenciesComputed = new HashSet<Function>(); // whether dependencies have already been computed
      while (functionDefs.Count > 0)
      {
        Function f = functionDefs.Peek();
        if (definitionAdded.Contains(f))
        {
          // This definition was already processed (as a dependency of another definition)
          functionDefs.Pop();
          continue;
        }

        // Grab the definition and then compute the dependencies.
        Contract.Assert(ctx.DefinedFunctions.ContainsKey(f));
        VCExprNAry defBody = ctx.DefinedFunctions[f];
        List<Function> dependencies = collector.Collect(defBody[1]);
        bool hasDependencies = false;
        foreach (Function fdep in dependencies)
        {
          if (ctx.DefinedFunctions.ContainsKey(fdep) && !definitionAdded.Contains(fdep))
          {
            if (!dependenciesComputed.Contains(fdep))
            {
              // Handle dependencies first
              functionDefs.Push(fdep);
              hasDependencies = true;
            }
            else
            {
              HandleProverError(
                "Function definition cycle detected: " + f.ToString() + " depends on " + fdep.ToString());
            }
          }
        }

        if (!hasDependencies)
        {
          // No dependencies: go ahead and process this definition.
          string funcDef = "(define-fun ";
          var funCall = defBody[0] as VCExprNAry;
          Contract.Assert(funCall != null);
          VCExprBoogieFunctionOp op = (VCExprBoogieFunctionOp) funCall.Op;
          Contract.Assert(op != null);
          funcDef += Namer.GetQuotedName(op.Func, op.Func.Name);

          funcDef += " (";
          foreach (var v in funCall.UniformArguments)
          {
            VCExprVar varExpr = v as VCExprVar;
            Contract.Assert(varExpr != null);
            DeclCollector.AddKnownVariable(varExpr); // add var to knows vars so that it does not get declared later on
            string printedName = Namer.GetQuotedLocalName(varExpr, varExpr.Name);
            Contract.Assert(printedName != null);
            funcDef += "(" + printedName + " " + SMTLibExprLineariser.TypeToString(varExpr.Type) + ") ";
          }

          funcDef += ") ";

          funcDef += SMTLibExprLineariser.TypeToString(defBody[0].Type) + " ";
          funcDef += VCExpr2String(defBody[1], -1);
          funcDef += ")";
          generatedFuncDefs.Add(funcDef);
          definitionAdded.Add(f);
          functionDefs.Pop();
        }
        else
        {
          dependenciesComputed.Add(f);
        }
      }

      FlushAxioms(); // Flush all dependencies before flushing function definitions
      generatedFuncDefs.Iter(SendCommon); // Flush function definitions
    }

    private void PrepareCommon()
    {
      if (common.Length == 0)
      {
        SendCommon("(set-option :print-success false)");
        SendCommon("(set-info :smt-lib-version 2.6)");
        if (options.ProduceModel())
          SendCommon("(set-option :produce-models true)");
        foreach (var opt in options.SmtOptions)
        {
          SendCommon("(set-option :" + opt.Option + " " + opt.Value + ")");
        }

        if (!string.IsNullOrEmpty(options.Logic))
        {
          SendCommon("(set-logic " + options.Logic + ")");
        }

        // Set produce-unsat-cores last. It seems there's a bug in Z3 where if we set it earlier its value
        // gets reset by other set-option commands ( https://z3.codeplex.com/workitem/188 )
        if (CommandLineOptions.Clo.PrintNecessaryAssumes || CommandLineOptions.Clo.EnableUnSatCoreExtract == 1 ||
            (CommandLineOptions.Clo.ContractInfer && (CommandLineOptions.Clo.UseUnsatCoreForContractInfer ||
                                                      CommandLineOptions.Clo.ExplainHoudini)))
        {
          SendCommon("(set-option :produce-unsat-cores true)");
          this.usingUnsatCore = true;
        }

        SendCommon("; done setting options\n");
        SendCommon(_backgroundPredicates);

        if (options.UseTickleBool)
        {
          SendCommon("(declare-fun tickleBool (Bool) Bool)");
          SendCommon("(assert (and (tickleBool true) (tickleBool false)))");
        }

        if (CommandLineOptions.Clo.RunDiagnosticsOnTimeout)
        {
          SendCommon("(declare-fun timeoutDiagnostics (Int) Bool)");
        }

        PrepareDataTypes();

        if (CommandLineOptions.Clo.ProverPreamble != null)
        {
          SendCommon("(include \"" + CommandLineOptions.Clo.ProverPreamble + "\")");
        }

        PrepareFunctionDefinitions();
      }

      if (!AxiomsAreSetup)
      {
        var axioms = ctx.Axioms;
        var nary = axioms as VCExprNAry;
        if (nary != null && nary.Op == VCExpressionGenerator.AndOp)
          foreach (var expr in nary.UniformArguments)
          {
            var str = VCExpr2String(expr, -1);
            if (str != "true")
              AddAxiom(str);
          }
        else
          AddAxiom(VCExpr2String(axioms, -1));

        AxiomsAreSetup = true;
        CachedAxBuilder = AxBuilder;
        CachedNamer = Namer;
      }
    }

    public override int FlushAxiomsToTheoremProver()
    {
      // we feed the axioms when BeginCheck is called.
      return 0;
    }

    private void FlushAndCacheCommons()
    {
      FlushAxioms();
      if (CachedCommon == null)
      {
        CachedCommon = common.ToString();
      }
    }

    private void FlushAxioms()
    {
      TypeDecls.Iter(SendCommon);
      TypeDecls.Clear();
      foreach (string s in Axioms)
      {
        Contract.Assert(s != null);
        if (s != "true")
          SendCommon("(assert " + s + ")");
      }

      Axioms.Clear();
      //FlushPushedAssertions();
    }

    private void CloseLogFile()
    {
      if (currentLogFile != null)
      {
        currentLogFile.Close();
        currentLogFile = null;
      }
    }

    private void FlushLogFile()
    {
      if (currentLogFile != null)
      {
        currentLogFile.Flush();
      }
    }

    public override void Close()
    {
      base.Close();
      CloseLogFile();
      if (Process != null)
        Process.Close();
    }

    public override void BeginCheck(string descriptiveName, VCExpr vc, ErrorHandler handler)
    {
      //Contract.Requires(descriptiveName != null);
      //Contract.Requires(vc != null);
      //Contract.Requires(handler != null);

      if (options.SeparateLogFiles) CloseLogFile(); // shouldn't really happen

      if (options.LogFilename != null && currentLogFile == null)
      {
        currentLogFile = OpenOutputFile(descriptiveName);
        currentLogFile.Write(common.ToString());
      }

      PrepareCommon();
      FlushAndCacheCommons();

      if (HasReset)
      {
        AxBuilder = (TypeAxiomBuilder) CachedAxBuilder?.Clone();
        Namer = (SMTLibNamer) CachedNamer.Clone();
        Namer.ResetLabelCount();
        DeclCollector.SetNamer(Namer);
        DeclCollector.Push();
      }

      OptimizationRequests.Clear();

      string vcString = "(assert (not\n" + VCExpr2String(vc, 1) + "\n))";
      FlushAxioms();

      PossiblyRestart();

      SendThisVC("(push 1)");
      SendThisVC("(set-info :boogie-vc-id " + SMTLibNamer.QuoteId(descriptiveName) + ")");
      if (options.Solver == SolverKind.Z3)
      {
        SendThisVC("(set-option :" + Z3.TimeoutOption + " " + options.TimeLimit + ")");
        SendThisVC("(set-option :" + Z3.RlimitOption + " " + options.ResourceLimit + ")");
        if (options.RandomSeed.HasValue)
        {
          SendThisVC("(set-option :" + Z3.RandomSeedOption + " " + options.RandomSeed.Value + ")");
        }
      }
      SendThisVC(vcString);

      SendOptimizationRequests();

      FlushLogFile();

      if (Process != null)
      {
        Process.PingPong(); // flush any errors

        if (Process.Inspector != null)
          Process.Inspector.NewProblem(descriptiveName);
      }

      if (HasReset)
      {
        DeclCollector.Pop();
        common = new StringBuilder(CachedCommon);
        HasReset = false;
      }

      SendCheckSat();
      FlushLogFile();
    }

    private void SendOptimizationRequests()
    {
      if (options.Solver == SolverKind.Z3 && 0 < OptimizationRequests.Count)
      {
        foreach (var r in OptimizationRequests)
        {
          SendThisVC(r);
        }
      }
    }

    public override void Reset(VCExpressionGenerator gen)
    {
      if (options.Solver == SolverKind.Z3)
      {
        this.gen = gen;
        SendThisVC("(reset)");

        if (0 < common.Length)
        {
          var c = common.ToString();
          Process.Send(c);
          if (currentLogFile != null)
          {
            currentLogFile.WriteLine(c);
          }
        }

        HasReset = true;
      }
    }

    public override void FullReset(VCExpressionGenerator gen)
    {
      if (options.Solver == SolverKind.Z3)
      {
        this.gen = gen;
        SendThisVC("(reset)");
        Namer.Reset();
        common.Clear();
        SetupAxiomBuilder(gen);
        Axioms.Clear();
        TypeDecls.Clear();
        AxiomsAreSetup = false;
        ctx.Reset();
        ctx.KnownDatatypes.Clear();
        ctx.parent = this;
        DeclCollector.Reset();
        NamedAssumes.Clear();
        UsedNamedAssumes = null;
        SendThisVC("; did a full reset");
      }
    }


    private string StripCruft(string name)
    {
      if (name.Contains("@@"))
        return name.Remove(name.LastIndexOf("@@"));
      return name;
    }

    private class BadExprFromProver : Exception
    {
    }

    private delegate VCExpr ArgGetter(int pos);

    private delegate VCExpr[] ArgsGetter();

    private delegate VCExprVar[] VarsGetter();

    private VCExprOp VCStringToVCOp(string op)
    {
      switch (op)
      {
        case "+":
          return VCExpressionGenerator.AddIOp;
        case "-":
          return VCExpressionGenerator.SubIOp;
        case "*":
          return VCExpressionGenerator.MulIOp;
        case "div":
          return VCExpressionGenerator.DivIOp;
        case "=":
          return VCExpressionGenerator.EqOp;
        case "<=":
          return VCExpressionGenerator.LeOp;
        case "<":
          return VCExpressionGenerator.LtOp;
        case ">=":
          return VCExpressionGenerator.GeOp;
        case ">":
          return VCExpressionGenerator.GtOp;
        case "and":
          return VCExpressionGenerator.AndOp;
        case "or":
          return VCExpressionGenerator.OrOp;
        case "not":
          return VCExpressionGenerator.NotOp;
        case "ite":
          return VCExpressionGenerator.IfThenElseOp;
        default:
          return null;
      }
    }

    private class MyDeclHandler : TypeDeclCollector.DeclHandler
    {
      public Dictionary<string, VCExprVar> var_map = new Dictionary<string, VCExprVar>();
      public Dictionary<string, Function> func_map = new Dictionary<string, Function>();

      public override void VarDecl(VCExprVar v)
      {
        var_map[v.Name] = v;
      }

      public override void FuncDecl(Function f)
      {
        func_map[f.Name] = f;
      }

      public MyDeclHandler()
      {
      }
    }

    private MyDeclHandler declHandler = null;

    private VCExprVar SExprToVar(SExpr e)
    {
      if (e.Arguments.Count() != 1)
      {
        HandleProverError("Prover error: bad quantifier syntax");
        throw new BadExprFromProver();
      }

      string vname = StripCruft(e.Name);
      SExpr vtype = e[0];
      switch (vtype.Name)
      {
        case "Int":
          return gen.Variable(vname, Type.Int);
        case "Bool":
          return gen.Variable(vname, Type.Bool);
        case "Array":
        {
          // TODO: handle more general array types
          var idxType = Type.Int; // well, could be something else
          var valueType =
            (vtype.Arguments[1].Name == "Int") ? Type.Int : Type.Bool;
          var types = new List<Type>();
          types.Add(idxType);
          return gen.Variable(vname, new MapType(Token.NoToken, new List<TypeVariable>(), types, valueType));
        }
        default:
        {
          HandleProverError("Prover error: bad type: " + vtype.Name);
          throw new BadExprFromProver();
        }
      }
    }

    private VCExpr MakeBinary(VCExprOp op, VCExpr[] args)
    {
      if (args.Count() == 0)
      {
        // with zero args we need the identity of the op
        if (op == VCExpressionGenerator.AndOp)
          return VCExpressionGenerator.True;
        if (op == VCExpressionGenerator.OrOp)
          return VCExpressionGenerator.False;
        if (op == VCExpressionGenerator.AddIOp)
        {
          Microsoft.BaseTypes.BigNum x = Microsoft.BaseTypes.BigNum.ZERO;
          return gen.Integer(x);
        }

        HandleProverError("Prover error: bad expression ");
        throw new BadExprFromProver();
      }

      var temp = args[0];
      for (int i = 1; i < args.Count(); i++)
        temp = gen.Function(op, temp, args[i]);
      return temp;
    }

    protected VCExpr SExprToVCExpr(SExpr e, Dictionary<string, VCExpr> bound)
    {
      if (e.Arguments.Count() == 0)
      {
        var name = StripCruft(e.Name);
        if (name[0] >= '0' && name[0] <= '9')
        {
          Microsoft.BaseTypes.BigNum x = Microsoft.BaseTypes.BigNum.FromString(name);
          return gen.Integer(x);
        }

        if (bound.ContainsKey(name))
        {
          return bound[name];
        }

        if (name == "true")
          return VCExpressionGenerator.True;
        if (name == "false")
          return VCExpressionGenerator.False;
        if (declHandler.var_map.ContainsKey(name))
          return declHandler.var_map[name];
        HandleProverError("Prover error: unknown symbol:" + name);
        //throw new BadExprFromProver ();
        var v = gen.Variable(name, Type.Int);
        bound.Add(name, v);
        return v;
      }

      ArgGetter g = i => SExprToVCExpr(e[i], bound);
      ArgsGetter ga = () => e.Arguments.Select(x => SExprToVCExpr(x, bound)).ToArray();
      VarsGetter gb = () => e[0].Arguments.Select(x => SExprToVar(x)).ToArray();
      switch (e.Name)
      {
        case "select":
          return gen.Select(ga());
        case "store":
          return gen.Store(ga());
        case "forall":
        case "exists":
        {
          var binds = e.Arguments[0];
          var vcbinds = new List<VCExprVar>();
          var bound_copy = new Dictionary<string, VCExpr>(bound);
          for (int i = 0; i < binds.Arguments.Count(); i++)
          {
            var bind = binds.Arguments[i];
            var symb = StripCruft(bind.Name);
            var vcv = SExprToVar(bind);
            vcbinds.Add(vcv);
            bound[symb] = vcv;
          }

          var body = g(1);
          if (e.Name == "forall")
            body = gen.Forall(vcbinds, new List<VCTrigger>(), body);
          else
            body = gen.Exists(vcbinds, new List<VCTrigger>(), body);
          bound = bound_copy;
          return body;
        }
        case "-": // have to deal with unary case
        {
          if (e.ArgCount == 1)
          {
            var args = new VCExpr[2];
            args[0] = gen.Integer(Microsoft.BaseTypes.BigNum.ZERO);
            args[1] = g(0);
            return gen.Function(VCStringToVCOp("-"), args);
          }

          return gen.Function(VCStringToVCOp("-"), ga());
        }
        case "!": // this is commentary
          return g(0);
        case "let":
        {
          // we expand lets exponentially since there is no let binding in Boogie surface syntax
          bool expand_lets = true;
          var binds = e.Arguments[0];
          var vcbinds = new List<VCExprLetBinding>();
          var bound_copy = new Dictionary<string, VCExpr>(bound);
          for (int i = 0; i < binds.Arguments.Count(); i++)
          {
            var bind = binds.Arguments[i];
            var symb = bind.Name;
            var def = bind.Arguments[0];
            var vce = SExprToVCExpr(def, bound);
            var vcv = gen.Variable(symb, vce.Type);
            var vcb = gen.LetBinding(vcv, vce);
            vcbinds.Add(vcb);
            bound[symb] = expand_lets ? vce : vcv;
          }

          var body = g(1);
          if (!expand_lets)
            body = gen.Let(vcbinds, body);
          bound = bound_copy;
          return body;
        }

        default:
        {
          var op = VCStringToVCOp(e.Name);
          if (op == null)
          {
            var name = StripCruft(e.Name);
            if (declHandler.func_map.ContainsKey(name))
            {
              Function f = declHandler.func_map[name];
              return gen.Function(f, ga());
            }

            HandleProverError("Prover error: unknown operator:" + e.Name);
            throw new BadExprFromProver();
          }

          if (op.Arity == 2)
            return MakeBinary(op, ga());
          return gen.Function(op, ga());
        }
      }
    }

    class MyFileParser : SExpr.Parser
    {
      SMTLibProcessTheoremProver parent;

      public MyFileParser(System.IO.StreamReader _sr, SMTLibProcessTheoremProver _parent)
        : base(_sr)
      {
        parent = _parent;
      }

      public override void ParseError(string msg)
      {
        parent.HandleProverError("Error in conjecture file from prover: " + msg);
      }
    }

    private static HashSet<string> usedLogNames = new HashSet<string>();

    private TextWriter OpenOutputFile(string descriptiveName)
    {
      Contract.Requires(descriptiveName != null);
      Contract.Ensures(Contract.Result<TextWriter>() != null);

      string filename = options.LogFilename;
      filename = Helpers.SubstituteAtPROC(descriptiveName, cce.NonNull(filename));
      var curFilename = filename;

      lock (usedLogNames)
      {
        int n = 1;
        while (usedLogNames.Contains(curFilename))
        {
          curFilename = filename + "." + n++;
        }

        usedLogNames.Add(curFilename);
      }

      return new StreamWriter(curFilename, false);
    }

    private void FlushProverWarnings()
    {
      var handler = currentErrorHandler;
      if (handler != null)
      {
        lock (proverWarnings)
        {
          proverWarnings.Iter(handler.OnProverWarning);
          proverWarnings.Clear();
        }
      }
    }

    private void ReportProverError(string err)
    {
      var handler = currentErrorHandler;
      if (handler != null)
      {
        handler.OnProverError(err);
      }
    }

    protected void HandleProverError(string s)
    {
      // Trying to match prover warnings of the form:
      // - for Z3: WARNING: warning_message
      // - for CVC4: query.smt2:222.24: warning: warning_message
      // All other lines are considered to be errors.

      s = s.Replace("\r", "");
      const string ProverWarning = "WARNING: ";
      string errors = "";

      lock (proverWarnings)
      {
        foreach (var line in s.Split('\n'))
        {
          int idx = line.IndexOf(ProverWarning, StringComparison.OrdinalIgnoreCase);
          if (idx >= 0)
          {
            string warn = line.Substring(idx + ProverWarning.Length);
            proverWarnings.Add(warn);
          }
          else
          {
            errors += (line + "\n");
          }
        }
      }

      FlushProverWarnings();

      if (errors == "") return;

      lock (proverErrors)
      {
        proverErrors.Add(errors);
        Console.WriteLine("Prover error: " + errors);
      }

      ReportProverError(errors);
    }

    [NoDefaultContract]
    public override Outcome CheckOutcome(ErrorHandler handler, int taskID = -1)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = CheckOutcomeCore(handler, taskID: taskID);
      SendThisVC("(pop 1)");
      FlushLogFile();

      return result;
    }

    [NoDefaultContract]
    public override Outcome CheckOutcomeCore(ErrorHandler handler, int taskID = -1)
    {
      Contract.EnsuresOnThrow<UnexpectedProverOutputException>(true);

      var result = Outcome.Undetermined;

      if (Process == null || proverErrors.Count > 0)
        return result;

      try
      {
        currentErrorHandler = handler;
        FlushProverWarnings();

        int errorLimit;
        if (CommandLineOptions.Clo.ConcurrentHoudini)
        {
          Contract.Assert(taskID >= 0);
          errorLimit = CommandLineOptions.Clo.Cho[taskID].ErrorLimit;
        }
        else
        {
          errorLimit = CommandLineOptions.Clo.ErrorLimit;
        }

        int errorsDiscovered = 0;

        var globalResult = Outcome.Undetermined;

        while (true)
        {
          string[] labels = null;
          bool popLater = false;

          try
          {
            errorsDiscovered++;

            result = GetResponse();

            var reporter = handler as VC.VCGen.ErrorReporter;
            // TODO(wuestholz): Is the reporter ever null?
            if (usingUnsatCore && result == Outcome.Valid && reporter != null && 0 < NamedAssumes.Count)
            {
              if (usingUnsatCore)
              {
                UsedNamedAssumes = new HashSet<string>();
                SendThisVC("(get-unsat-core)");
                var resp = Process.GetProverResponse();
                if (resp.Name != "")
                {
                  UsedNamedAssumes.Add(resp.Name);
                  if (CommandLineOptions.Clo.PrintNecessaryAssumes)
                  {
                    reporter.AddNecessaryAssume(resp.Name.Substring("aux$$assume$$".Length));
                  }
                }

                foreach (var arg in resp.Arguments)
                {
                  UsedNamedAssumes.Add(arg.Name);
                  if (CommandLineOptions.Clo.PrintNecessaryAssumes)
                  {
                    reporter.AddNecessaryAssume(arg.Name.Substring("aux$$assume$$".Length));
                  }
                }
              }
              else
              {
                UsedNamedAssumes = null;
              }
            }

            if (CommandLineOptions.Clo.RunDiagnosticsOnTimeout && result == Outcome.TimeOut)
            {
              #region Run timeout diagnostics

              if (CommandLineOptions.Clo.TraceDiagnosticsOnTimeout)
              {
                Console.Out.WriteLine("Starting timeout diagnostics with initial time limit {0}.", options.TimeLimit);
              }

              SendThisVC("; begin timeout diagnostics");

              var start = DateTime.UtcNow;
              var unverified = new SortedSet<int>(ctx.TimeoutDiagnosticIDToAssertion.Keys);
              var timedOut = new SortedSet<int>();
              int frac = 2;
              int queries = 0;
              int timeLimitPerAssertion = 0 < options.TimeLimit
                ? (options.TimeLimit / 100) * CommandLineOptions.Clo.TimeLimitPerAssertionInPercent
                : 1000;
              while (true)
              {
                int rem = unverified.Count;
                if (rem == 0)
                {
                  if (0 < timedOut.Count)
                  {
                    result = CheckSplit(timedOut, ref popLater, options.TimeLimit, timeLimitPerAssertion, ref queries);
                    if (result == Outcome.Valid)
                    {
                      timedOut.Clear();
                    }
                    else if (result == Outcome.TimeOut)
                    {
                      // Give up and report which assertions were not verified.
                      var cmds = timedOut.Select(id => ctx.TimeoutDiagnosticIDToAssertion[id]);

                      if (cmds.Any())
                      {
                        handler.OnResourceExceeded("timeout after running diagnostics", cmds);
                      }
                    }
                  }
                  else
                  {
                    result = Outcome.Valid;
                  }

                  break;
                }

                // TODO(wuestholz): Try out different ways for splitting up the work (e.g., randomly).
                var cnt = Math.Max(1, rem / frac);
                // It seems like assertions later in the control flow have smaller indexes.
                var split = new SortedSet<int>(unverified.Where((val, idx) => (rem - idx - 1) < cnt));
                Contract.Assert(0 < split.Count);
                var splitRes = CheckSplit(split, ref popLater, timeLimitPerAssertion, timeLimitPerAssertion,
                  ref queries);
                if (splitRes == Outcome.Valid)
                {
                  unverified.ExceptWith(split);
                  frac = 1;
                }
                else if (splitRes == Outcome.Invalid)
                {
                  result = splitRes;
                  break;
                }
                else if (splitRes == Outcome.TimeOut)
                {
                  if (2 <= frac && (4 <= (rem / frac)))
                  {
                    frac *= 4;
                  }
                  else if (2 <= (rem / frac))
                  {
                    frac *= 2;
                  }
                  else
                  {
                    timedOut.UnionWith(split);
                    unverified.ExceptWith(split);
                    frac = 1;
                  }
                }
                else
                {
                  break;
                }
              }

              unverified.UnionWith(timedOut);

              var end = DateTime.UtcNow;

              SendThisVC("; end timeout diagnostics");

              if (CommandLineOptions.Clo.TraceDiagnosticsOnTimeout)
              {
                Console.Out.WriteLine("Terminated timeout diagnostics after {0:F0} ms and {1} prover queries.",
                  end.Subtract(start).TotalMilliseconds, queries);
                Console.Out.WriteLine("Outcome: {0}", result);
                Console.Out.WriteLine("Unverified assertions: {0} (of {1})", unverified.Count,
                  ctx.TimeoutDiagnosticIDToAssertion.Keys.Count);

                string filename = "unknown";
                var assertion = ctx.TimeoutDiagnosticIDToAssertion.Values.Select(t => t.Item1)
                  .FirstOrDefault(a => a.tok != null && a.tok != Token.NoToken && a.tok.filename != null);
                if (assertion != null)
                {
                  filename = assertion.tok.filename;
                }

                File.AppendAllText("timeouts.csv",
                  string.Format(";{0};{1};{2:F0};{3};{4};{5};{6}\n", filename, options.TimeLimit,
                    end.Subtract(start).TotalMilliseconds, queries, result, unverified.Count,
                    ctx.TimeoutDiagnosticIDToAssertion.Keys.Count));
              }

              #endregion
            }

            if (globalResult == Outcome.Undetermined)
              globalResult = result;

            if (result == Outcome.Invalid)
            {
              Model model = GetErrorModel();
              if (CommandLineOptions.Clo.SIBoolControlVC)
              {
                labels = new string[0];
              }
              else
              {
                labels = CalculatePath(handler.StartingProcId());
                if (labels.Length == 0)
                {
                  // Without a path to an error, we don't know what to report
                  globalResult = Outcome.Undetermined;
                  break;
                }
              }

              handler.OnModel(labels, model, result);
            }

            Debug.Assert(errorsDiscovered > 0);
            // if errorLimit is 0, loop will break only if there are no more 
            // counterexamples to be discovered.
            if (labels == null || !labels.Any() || errorsDiscovered == errorLimit) break;
          }
          finally
          {
            if (popLater)
            {
              SendThisVC("(pop 1)");
            }
          }

          {
            string source = labels[labels.Length - 2];
            string target = labels[labels.Length - 1];
            // block the assert which was falsified by this counterexample
            SendThisVC("(assert (not (= (ControlFlow 0 " + source + ") (- " + target + "))))");
            SendCheckSat();
          }
        }

        FlushLogFile();

        if (CommandLineOptions.Clo.RestartProverPerVC && Process != null)
          Process.NeedsRestart = true;

        return globalResult;
      }
      finally
      {
        currentErrorHandler = null;
      }
    }

    private Outcome CheckSplit(SortedSet<int> split, ref bool popLater, int timeLimit, int timeLimitPerAssertion,
      ref int queries)
    {
      var tla = timeLimitPerAssertion * split.Count;

      if (popLater)
      {
        SendThisVC("(pop 1)");
      }

      SendThisVC("(push 1)");
      // FIXME: Gross. Timeout should be set in one place! This is also Z3 specific!
      int newTimeout = (0 < tla && tla < timeLimit) ? tla : timeLimit;
      if (newTimeout > 0)
      {
        SendThisVC(string.Format("(set-option :{0} {1})", Z3.TimeoutOption, newTimeout));
      }

      popLater = true;

      SendThisVC(string.Format("; checking split VC with {0} unverified assertions", split.Count));
      var expr = VCExpressionGenerator.True;
      foreach (var i in ctx.TimeoutDiagnosticIDToAssertion.Keys)
      {
        var lit = VCExprGen.Function(VCExpressionGenerator.TimeoutDiagnosticsOp,
          VCExprGen.Integer(Microsoft.BaseTypes.BigNum.FromInt(i)));
        if (split.Contains(i))
        {
          lit = VCExprGen.Not(lit);
        }

        expr = VCExprGen.AndSimp(expr, lit);
      }

      SendThisVC("(assert " + VCExpr2String(expr, 1) + ")");
      if (options.Solver == SolverKind.Z3)
      {
        SendThisVC("(apply (then (using-params propagate-values :max_rounds 1) simplify) :print false)");
      }

      FlushLogFile();
      SendCheckSat();
      queries++;
      return GetResponse();
    }

    public override string[] CalculatePath(int controlFlowConstant)
    {
      SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " 0)))");
      var path = new List<string>();
      while (true)
      {
        var resp = Process.GetProverResponse();
        if (resp == null) break;
        if (!(resp.Name == "" && resp.ArgCount == 1)) break;
        resp = resp.Arguments[0];
        if (!(resp.Name == "" && resp.ArgCount == 2)) break;
        resp = resp.Arguments[1];
        var v = resp.Name;
        if (v == "-" && resp.ArgCount == 1)
        {
          v = resp.Arguments[0].Name;
          path.Add(v);
          break;
        }
        else if (resp.ArgCount != 0)
          break;

        path.Add(v);
        SendThisVC("(get-value ((ControlFlow " + controlFlowConstant + " " + v + ")))");
      }

      return path.ToArray();
    }


    private class SMTErrorModelConverter
    {
      private List<SExpr> ErrorModelTodo;
      private SMTLibProcessTheoremProver Parent;
      private StringBuilder ErrorModel = new StringBuilder();
      private HashSet<SExpr> TopLevelProcessed = new HashSet<SExpr>();
      private int NumNewArrays = 0;
      private Dictionary<string, int> SortSet = new Dictionary<string, int>();

      private Dictionary<string, Dictionary<string, List<SExpr>>> DataTypes =
        new Dictionary<string, Dictionary<string, List<SExpr>>>();

      private Dictionary<string, SExpr> Functions = new Dictionary<string, SExpr>();

      public SMTErrorModelConverter(SExpr _ErrorModel, SMTLibProcessTheoremProver _Parent)
      {
        ErrorModelTodo = _ErrorModel.Arguments.ToList();
        Parent = _Parent;
      }

      public string Convert()
      {
        ConvertErrorModel(ErrorModel);
        return ErrorModel.ToString();
      }

      bool isConstArray(SExpr element, SExpr type)
      {
        if (type.Name != "Array")
          return false;

        if (element.Name == "__array_store_all__") // CVC4 1.4
          return true;
        else if (element.Name == "" && element[0].Name == "as" &&
                 element[0][0].Name == "const") // CVC4 > 1.4
          return true;

        return false;
      }

      SExpr getConstArrayElement(SExpr element)
      {
        if (element.Name == "__array_store_all__") // CVC4 1.4
          return element[1];
        else if (element.Name == "" && element[0].Name == "as" &&
                 element[0][0].Name == "const") // CVC4 > 1.4
          return element[1];

        Parent.HandleProverError("Unexpected value: " + element);
        throw new BadExprFromProver();
      }

      void ConstructComplexValue(SExpr element, SExpr type, StringBuilder m)
      {
        if (type.Name == "Array")
        {
          if (element.Name == "store" || isConstArray(element, type))
          {
            NumNewArrays++;
            m.Append("as-array[k!" + NumNewArrays + ']');
            SExpr[] args = {new SExpr("k!" + NumNewArrays), new SExpr(""), type, element};
            var newElement = new SExpr("define-fun", args);
            TopLevelProcessed.Add(newElement);
            ErrorModelTodo.Add(newElement);
            return;
          }
        }

        ConstructSimpleValue(element, type, m);
      }

      void ConstructSimpleValue(SExpr element, SExpr type, StringBuilder m)
      {
        if (type.Name == "Bool" && element.ArgCount == 0)
        {
          m.Append(element.ToString());
          return;
        }

        if (type.Name == "Int")
        {
          if (element.ArgCount == 0)
          {
            m.Append(element.ToString());
            return;
          }
          else if (element.Name == "-" && element.ArgCount == 1)
          {
            m.Append(element.ToString());
            return;
          }
        }

        if (type.Name == "_" && type.ArgCount == 2 && type[0].Name == "BitVec")
        {
          if (element.Name == "_" && element.ArgCount == 2 &&
              element[0].Name.StartsWith("bv") && element[0].ArgCount == 0 &&
              element[1].Name == type.Arguments[1].Name && element[1].ArgCount == 0)
          {
            m.Append(element[0].Name + '[' + element[1].Name + ']');
            return;
          }
        }

        if (type.Name == "Array")
        {
          while (element.Name == "store")
          {
            ConstructComplexValue(element[1], type[0], m);
            m.Append(" -> ");
            ConstructComplexValue(element[2], type[1], m);
            m.Append("\n  ");
            if (element[0].Name != "store")
            {
              m.Append("else -> ");
            }

            element = element[0];
          }

          if (isConstArray(element, type))
          {
            ConstructComplexValue(getConstArrayElement(element), type[1], m);
            return;
          }
          else if (element.Name == "_" && element.ArgCount == 2 &&
                   element[0].Name == "as-array")
          {
            m.Append("as-array[" + element[1].Name + ']');
            return;
          }
        }

        if (SortSet.ContainsKey(type.Name) && SortSet[type.Name] == 0)
        {
          var prefix = "@uc_T@" + type.Name.Substring(2) + "_";
          if (element.Name.StartsWith(prefix))
          {
            m.Append(type.Name + "!val!" + element.Name.Substring(prefix.Length));
            return;
          }
        }

        if (Functions.ContainsKey(element.Name) &&
            type.Name == Functions[element.Name].Name)
        {
          m.Append(element.Name);
          return;
        }

        if (DataTypes.ContainsKey(type.Name) &&
            DataTypes[type.Name].ContainsKey(element.Name) &&
            element.ArgCount == DataTypes[type.Name][element.Name].Count)
        {
          m.Append("(" + element.Name);
          for (int i = 0; i < element.ArgCount; ++i)
          {
            m.Append(" ");
            ConstructComplexValue(element[i], DataTypes[type.Name][element.Name][i], m);
          }

          m.Append(")");
          return;
        }

        Parent.HandleProverError("Unexpected value: " + element);
        throw new BadExprFromProver();
      }

      void ConstructFunctionArguments(SExpr arguments, List<SExpr> argTypes, StringBuilder[] argValues)
      {
        if (arguments.Name == "and")
        {
          ConstructFunctionArguments(arguments[0], argTypes, argValues);
          ConstructFunctionArguments(arguments[1], argTypes, argValues);
        }
        else if (arguments.Name == "=" &&
                 (arguments[0].Name.StartsWith("_ufmt_") || arguments[0].Name.StartsWith("x!") ||
                  arguments[0].Name.StartsWith("_arg_")))
        {
          int argNum;
          if (arguments[0].Name.StartsWith("_ufmt_"))
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("_uftm_".Length)) - 1;
          else if (arguments[0].Name.StartsWith("_arg_"))
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("_arg_".Length)) - 1;
          else /* if (arguments[0].Name.StartsWith("x!")) */
            argNum = System.Convert.ToInt32(arguments[0].Name.Substring("x!".Length)) - 1;
          if (argNum < 0 || argNum >= argTypes.Count)
          {
            Parent.HandleProverError("Unexpected function argument: " + arguments[0]);
            throw new BadExprFromProver();
          }

          if (argValues[argNum] != null)
          {
            Parent.HandleProverError("Function argument defined multiple times: " + arguments[0]);
            throw new BadExprFromProver();
          }

          argValues[argNum] = new StringBuilder();
          ConstructComplexValue(arguments[1], argTypes[argNum], argValues[argNum]);
        }
        else
        {
          Parent.HandleProverError("Unexpected function argument: " + arguments);
          throw new BadExprFromProver();
        }
      }

      void ConstructFunctionElements(SExpr element, List<SExpr> argTypes, SExpr outType, StringBuilder m)
      {
        while (element.Name == "ite")
        {
          StringBuilder[] argValues = new StringBuilder[argTypes.Count];
          ConstructFunctionArguments(element[0], argTypes, argValues);
          foreach (var s in argValues)
            m.Append(s + " ");
          m.Append("-> ");
          ConstructComplexValue(element[1], outType, m);
          m.Append("\n  ");
          if (element[2].Name != "ite")
            m.Append("else -> ");
          element = element[2];
        }

        ConstructComplexValue(element, outType, m);
      }

      void ConstructFunction(SExpr element, SExpr inType, SExpr outType, StringBuilder m)
      {
        List<SExpr> argTypes = new List<SExpr>();

        for (int i = 0; i < inType.ArgCount; ++i)
        {
          if (inType[i].Name != "_ufmt_" + (i + 1) && inType[i].Name != "x!" + (i + 1) &&
              !inType[i].Name.StartsWith("BOUND_VARIABLE_") && inType[i].Name != "_arg_" + (i + 1))
          {
            Parent.HandleProverError("Unexpected function argument: " + inType[i].Name);
            throw new BadExprFromProver();
          }

          argTypes.Add(inType[i][0]);
        }

        ConstructFunctionElements(element, argTypes, outType, m);
      }

      void ConstructDefine(SExpr element, StringBuilder m)
      {
        Debug.Assert(element.Name == "define-fun");

        if (element[1].ArgCount != 0)
          TopLevelProcessed.Add(element);

        m.Append(element[0] + " -> ");
        if (TopLevelProcessed.Contains(element))
          m.Append("{\n  ");

        if (element[1].ArgCount == 0 && element[2].Name == "Array" && !TopLevelProcessed.Contains(element))
        {
          ConstructComplexValue(element[3], element[2], m);
        }
        else if (element[1].ArgCount == 0)
        {
          ConstructSimpleValue(element[3], element[2], m);
        }
        else
        {
          ConstructFunction(element[3], element[1], element[2], m);
        }

        if (TopLevelProcessed.Contains(element))
          m.Append("\n}");
        m.Append("\n");
      }

      void ExtractDataType(SExpr datatypes)
      {
        Debug.Assert(datatypes.Name == "declare-datatypes");

        if (datatypes[0].Name != "" || datatypes[1].Name != "" || datatypes[1].ArgCount != 1)
        {
          Parent.HandleProverError("Unexpected datatype: " + datatypes);
          throw new BadExprFromProver();
        }

        SExpr typeDef = datatypes[1][0];
        Dictionary<string, List<SExpr>> dataTypeConstructors = new Dictionary<string, List<SExpr>>();
        for (int j = 0; j < typeDef.ArgCount; ++j)
        {
          var argumentTypes = new List<SExpr>();
          for (int i = 0; i < typeDef[j].ArgCount; ++i)
          {
            if (typeDef[j][i].ArgCount != 1)
            {
              Parent.HandleProverError("Unexpected datatype constructor: " + typeDef[j]);
              throw new BadExprFromProver();
            }

            argumentTypes.Add(typeDef[j][i][0]);
          }

          dataTypeConstructors[typeDef[j].Name] = argumentTypes;
        }

        DataTypes[datatypes[0][0].Name] = dataTypeConstructors;
      }

      private void ConvertErrorModel(StringBuilder m)
      {
        if (Parent.options.Solver == SolverKind.Z3)
        {
          // Datatype declarations are not returned by Z3, so parse common
          // instead. This is not very efficient, but currently not an issue,
          // as this not the normal way of interfacing with Z3.
          var ms = new MemoryStream(Encoding.ASCII.GetBytes(Parent.common.ToString()));
          var sr = new StreamReader(ms);
          SExpr.Parser p = new MyFileParser(sr, null);
          var sexprs = p.ParseSExprs(false);
          foreach (var e in sexprs)
          {
            switch (e.Name)
            {
              case "declare-datatypes":
                ExtractDataType(e);
                break;
            }
          }
        }

        while (ErrorModelTodo.Count > 0)
        {
          var e = ErrorModelTodo[0];
          ErrorModelTodo.RemoveAt(0);

          switch (e.Name)
          {
            case "define-fun":
              ConstructDefine(e, m);
              break;
            case "declare-sort":
              SortSet[e[0].Name] = System.Convert.ToInt32(e[1].Name);
              break;
            case "declare-datatypes":
              ExtractDataType(e);
              break;
            case "declare-fun":
              if (e[1].Name != "" || e[1].ArgCount > 0 || e[2].ArgCount > 0 ||
                  e[2].Name == "Bool" || e[2].Name == "Int")
              {
                Parent.HandleProverError("Unexpected top level model element: " + e.Name);
                throw new BadExprFromProver();
              }

              Functions[e[0].Name] = e[2];
              break;
            case "forall":
              // ignore
              break;
            default:
              Parent.HandleProverError("Unexpected top level model element: " + e.Name);
              throw new BadExprFromProver();
          }
        }
      }
    }

    private Model GetErrorModel()
    {
      if (!options.ExpectingModel())
        return null;

      SendThisVC("(get-model)");
      Process.Ping();
      Model theModel = null;
      while (true)
      {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
          break;
        if (theModel != null)
          HandleProverError("Expecting only one model but got many");

        string modelStr = null;
        if (resp.Name == "model" && resp.ArgCount >= 1)
        {
          var converter = new SMTErrorModelConverter(resp, this);
          modelStr = converter.Convert();
        }
        else if (resp.ArgCount == 0 && resp.Name.Contains("->"))
        {
          modelStr = resp.Name;
        }
        else
        {
          HandleProverError("Unexpected prover response getting model: " + resp.ToString());
        }

        List<Model> models = null;
        try
        {
          switch (options.Solver)
          {
            case SolverKind.Z3:
            case SolverKind.CVC4:
              models = Model.ParseModels(new StringReader("Error model: \n" + modelStr));
              break;
            default:
              Debug.Assert(false);
              return null;
          }
        }
        catch (ArgumentException exn)
        {
          HandleProverError("Model parsing error: " + exn.Message);
        }

        if (models == null)
          HandleProverError("Could not parse any models");
        else if (models.Count == 0)
          HandleProverError("Could not parse any models");
        else if (models.Count > 1)
          HandleProverError("Expecting only one model but got many");
        else
          theModel = models[0];
      }

      return theModel;
    }

    private string[] GetLabelsInfo()
    {
      SendThisVC("(labels)");
      Process.Ping();

      string[] res = null;
      while (true)
      {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
          break;
        if (res != null)
          HandleProverError("Expecting only one sequence of labels but got many");
        if (resp.Name == "labels")
        {
          res = resp.Arguments.Select(a => Namer.AbsyLabel(a.Name.Replace("|", ""))).ToArray();
        }
        else
        {
          HandleProverError("Unexpected prover response getting labels: " + resp.ToString());
        }
      }

      return res;
    }

    private Outcome GetResponse()
    {
      var result = Outcome.Undetermined;
      var wasUnknown = false;

      Process.Ping();

      while (true)
      {
        var resp = Process.GetProverResponse();
        if (resp == null || Process.IsPong(resp))
          break;

        switch (resp.Name)
        {
          case "unsat":
            result = Outcome.Valid;
            break;
          case "sat":
            result = Outcome.Invalid;
            break;
          case "unknown":
            result = Outcome.Invalid;
            wasUnknown = true;
            break;
          case "objectives":
            // We ignore this.
            break;
          case "error":
            if (resp.Arguments.Length == 1 && resp.Arguments[0].IsId &&
                (resp.Arguments[0].Name.Contains("max. resource limit exceeded")
                 || resp.Arguments[0].Name.Contains("resource limits reached")))
            {
              currentErrorHandler.OnResourceExceeded("max resource limit");
              result = Outcome.OutOfResource;
            }
            else
            {
              HandleProverError("Unexpected prover response: " + resp.ToString());
            }

            break;
          default:
            HandleProverError("Unexpected prover response: " + resp.ToString());
            break;
        }
      }

      if (wasUnknown)
      {
        SendThisVC("(get-info :reason-unknown)");
        Process.Ping();
        while (true)
        {
          var resp = Process.GetProverResponse();
          if (resp == null || Process.IsPong(resp))
            break;

          if (resp.ArgCount == 1 && resp.Name == ":reason-unknown")
          {
            switch (resp[0].Name)
            {
              case "incomplete":
              case "(incomplete quantifiers)":
              case "(incomplete (theory arithmetic))":
              case "smt tactic failed to show goal to be sat/unsat (incomplete (theory arithmetic))":
                break;
              case "memout":
                currentErrorHandler.OnResourceExceeded("memory");
                result = Outcome.OutOfMemory;
                Process.NeedsRestart = true;
                break;
              case "timeout":
                currentErrorHandler.OnResourceExceeded("timeout");
                result = Outcome.TimeOut;
                break;
              case "canceled":
                // both timeout and max resource limit are reported as
                // canceled in version 4.4.1 
                if (this.options.TimeLimit > 0)
                {
                  currentErrorHandler.OnResourceExceeded("timeout");
                  result = Outcome.TimeOut;
                }
                else
                {
                  currentErrorHandler.OnResourceExceeded("max resource limit");
                  result = Outcome.OutOfResource;
                }

                break;
              case "max. resource limit exceeded":
              case "resource limits reached":
              case "(resource limits reached)":
                currentErrorHandler.OnResourceExceeded("max resource limit");
                result = Outcome.OutOfResource;
                break;
              default:
                result = Outcome.Undetermined;
                HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp.ToString());
                break;
            }
          }
          else
          {
            result = Outcome.Undetermined;
            HandleProverError("Unexpected prover response (getting info about 'unknown' response): " + resp.ToString());
          }
        }
      }

      return result;
    }

    readonly IList<string> OptimizationRequests = new List<string>();

    protected string VCExpr2String(VCExpr expr, int polarity)
    {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<string>() != null);

      lock (gen)
      {
        DateTime start = DateTime.UtcNow;
        //if (CommandLineOptions.Clo.Trace)
        //  Console.Write("Linearising ... ");

        // handle the types in the VCExpr
        VCExpr exprWithoutTypes;
        switch (CommandLineOptions.Clo.TypeEncodingMethod)
        {
          case CommandLineOptions.TypeEncoding.Arguments:
          {
            TypeEraser eraser = new TypeEraserArguments((TypeAxiomBuilderArguments) AxBuilder, gen);
            exprWithoutTypes = AxBuilder.Cast(eraser.Erase(expr, polarity), Type.Bool);
            break;
          }
          case CommandLineOptions.TypeEncoding.Monomorphic:
          {
            exprWithoutTypes = expr;
            break;
          }
          default:
          {
            TypeEraser eraser = new TypeEraserPremisses((TypeAxiomBuilderPremisses) AxBuilder, gen);
            exprWithoutTypes =  AxBuilder.Cast(eraser.Erase(expr, polarity), Type.Bool);
            break;
          }
        }
        Contract.Assert(exprWithoutTypes != null);

        LetBindingSorter letSorter = new LetBindingSorter(gen);
        Contract.Assert(letSorter != null);

        VCExpr sortedExpr = letSorter.Mutate(exprWithoutTypes, true);
        Contract.Assert(sortedExpr != null);
        DeclCollector.Collect(sortedExpr);
        FeedTypeDeclsToProver();

        if (AxBuilder != null)
        {
          VCExpr sortedAxioms = letSorter.Mutate(AxBuilder.GetNewAxioms(), true);
          Contract.Assert(sortedAxioms != null);
          DeclCollector.Collect(sortedAxioms);
          FeedTypeDeclsToProver();
          AddAxiom(SMTLibExprLineariser.ToString(sortedAxioms, Namer, options, namedAssumes: NamedAssumes));
        }

        string res = SMTLibExprLineariser.ToString(sortedExpr, Namer, options, NamedAssumes, OptimizationRequests);
        Contract.Assert(res != null);

        if (CommandLineOptions.Clo.Trace)
        {
          DateTime end = DateTime.UtcNow;
          TimeSpan elapsed = end - start;
          if (elapsed.TotalSeconds > 0.5)
            Console.WriteLine("Linearising   [{0} s]", elapsed.TotalSeconds);
        }

        return res;
      }
    }

    // the list of all known axioms, where have to be included in each
    // verification condition
    private readonly List<string /*!>!*/> Axioms = new List<string /*!*/>();
    private bool AxiomsAreSetup = false;
    private bool HasReset = false;


    // similarly, a list of function/predicate declarations
    private readonly List<string /*!>!*/> TypeDecls = new List<string /*!*/>();

    protected void AddAxiom(string axiom)
    {
      Contract.Requires(axiom != null);
      Axioms.Add(axiom);
      //      if (thmProver != null) {
      //        LogActivity(":assume " + axiom);
      //        thmProver.AddAxioms(axiom);
      //      }
    }

    protected void AddTypeDecl(string decl)
    {
      Contract.Requires(decl != null);
      TypeDecls.Add(decl);
      //     if (thmProver != null) {
      //       LogActivity(decl);
      //       thmProver.Feed(decl, 0);
      //     }
    }

    ////////////////////////////////////////////////////////////////////////////

    private static string _backgroundPredicates;

    static void InitializeGlobalInformation()
    {
      Contract.Ensures(_backgroundPredicates != null);
      //throws ProverException, System.IO.FileNotFoundException;
      if (_backgroundPredicates == null)
      {
        if (CommandLineOptions.Clo.TypeEncodingMethod == CommandLineOptions.TypeEncoding.Monomorphic)
        {
          _backgroundPredicates = "";
        }
        else
        {
          _backgroundPredicates = @"
(set-info :category ""industrial"")
(declare-sort |T@U| 0)
(declare-sort |T@T| 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (|T@U| |T@U|) Bool)
(declare-fun UOrdering3 (|T@T| |T@U| |T@U|) Bool)";
        }
      }
    }

    public override VCExpressionGenerator VCExprGen
    {
      get { return this.gen; }
    }

    //// Push/pop interface

    //List<string> pushedAssertions = new List<string>();
    //int numRealPushes;
    public override string VCExpressionToString(VCExpr vc)
    {
      return VCExpr2String(vc, 1);
    }

    public override void PushVCExpression(VCExpr vc)
    {
      throw new NotImplementedException();
    }

    public override void Pop()
    {
      SendThisVC("(pop 1)");
      DeclCollector.Pop();
    }

    public override int NumAxiomsPushed()
    {
      throw new NotImplementedException();
      //return numRealPushes + pushedAssertions.Count;
    }

    private void FlushPushedAssertions()
    {
      throw new NotImplementedException();
    }

    public override void Assert(VCExpr vc, bool polarity, bool isSoft = false, int weight = 1, string name = null)
    {
      OptimizationRequests.Clear();
      string assert = "assert";
      if (options.Solver == SolverKind.Z3 && isSoft)
      {
        assert += "-soft";
      }

      var expr = polarity ? VCExpr2String(vc, 1) : "(not\n" + VCExpr2String(vc, 1) + "\n)";
      if (options.Solver == SolverKind.Z3 && isSoft)
      {
        expr += " :weight " + weight;
      }

      if (name != null)
      {
        expr = "(! " + expr + ":named " + name + ")";
      }

      AssertAxioms();
      SendThisVC("(" + assert + " " + expr + ")");
      SendOptimizationRequests();
    }

    public override List<string> UnsatCore()
    {
      SendThisVC("(get-unsat-core)");
      var resp = Process.GetProverResponse().ToString();
      if (resp == "" || resp == "()")
        return null;
      if (resp[0] == '(')
        resp = resp.Substring(1, resp.Length - 2);
      var ucore = resp.Split(' ').ToList();
      return ucore;
    }

    public override void DefineMacro(Macro f, VCExpr vc)
    {
      DeclCollector.AddKnownFunction(f);
      string printedName = Namer.GetQuotedName(f, f.Name);
      var argTypes = f.InParams.Cast<Variable>().MapConcat(p => DeclCollector.TypeToStringReg(p.TypedIdent.Type), " ");
      string decl = "(define-fun " + printedName + " (" + argTypes + ") " +
                    DeclCollector.TypeToStringReg(f.OutParams[0].TypedIdent.Type) + " " + VCExpr2String(vc, 1) + ")";
      AssertAxioms();
      SendThisVC(decl);
    }

    public override void AssertAxioms()
    {
      FlushAxioms();
    }

    public override void Check()
    {
      PrepareCommon();
      SendCheckSat();
      FlushLogFile();
    }

    public void SendCheckSat()
    {
      UsedNamedAssumes = null;
      SendThisVC("(check-sat)");
    }

    public override void SetTimeout(int ms)
    {
      options.TimeLimit = ms;
    }

    public override void SetRlimit(int limit)
    {
      options.ResourceLimit = limit;
    }

    public override void SetRandomSeed(int? randomSeed)
    {
      options.RandomSeed = randomSeed;
    }
    
    object ParseValueFromProver(SExpr expr)
    {
      return expr.ToString().Replace(" ", "").Replace("(", "").Replace(")", "");
    }

    SExpr ReduceLet(SExpr expr)
    {
      if (expr.Name != "let")
        return expr;

      var bindings = expr.Arguments[0].Arguments;
      var subexpr = expr.Arguments[1];

      var dict = new Dictionary<string, SExpr>();
      foreach (var binding in bindings)
      {
        Contract.Assert(binding.ArgCount == 1);
        dict.Add(binding.Name, binding.Arguments[0]);
      }

      Contract.Assert(!dict.ContainsKey(subexpr.Name));

      var workList = new Stack<SExpr>();
      workList.Push(subexpr);
      while (workList.Count > 0)
      {
        var curr = workList.Pop();
        for (int i = 0; i < curr.ArgCount; i++)
        {
          var arg = curr.Arguments[i];
          if (dict.ContainsKey(arg.Name))
            curr.Arguments[i] = dict[arg.Name];
          else
            workList.Push(arg);
        }
      }

      return subexpr;
    }

    object GetArrayFromProverResponse(SExpr resp)
    {
      resp = ReduceLet(resp);
      var dict = GetArrayFromArrayExpr(resp);
      if (dict == null) dict = GetArrayFromProverLambdaExpr(resp);
      if (dict == null) return null;
      var str = new StringWriter();
      str.Write("{");
      foreach (var entry in dict)
        if (entry.Key != "*")
          str.Write("\"{0}\":{1},", entry.Key, entry.Value);
      if (dict.ContainsKey("*"))
        str.Write("\"*\":{0}", dict["*"]);
      str.Write("}");
      return str.ToString();
    }

    Dictionary<string, object> GetArrayFromProverLambdaExpr(SExpr resp)
    {
      var dict = new Dictionary<string, object>();
      if (resp.Name == "lambda" && resp.ArgCount == 2)
      {
        // TODO: multiple indices, as (lambda (() (x!1 Int) (x!2 Int)) ...)
        var indexVar = resp.Arguments[0].Arguments[0].Name;

        var cases = resp.Arguments[1];
        while (cases != null)
        {
          if (cases.Name == "ite")
          {
            var condition = cases.Arguments[0];
            var positive = cases.Arguments[1];
            var negative = cases.Arguments[2];

            // TODO: multiple index conditions, as (and (= x!1 5) (= x!2 3))
            // TODO: nested arrays, as (ite (...) (_ as-array k!5) (_ as-array k!3))

            if (condition.Name != "=")
              throw new VCExprEvaluationException();

            if (condition.Arguments[0].Name != indexVar)
              throw new VCExprEvaluationException();

            var index = ParseValueFromProver(condition.Arguments[1]);
            var value = ParseValueFromProver(positive);

            dict.Add(index.ToString(), value);

            cases = negative;
          }
          else if (cases.IsId)
          {
            var value = ParseValueFromProver(cases);
            dict.Add("*", value);
            cases = null;
          }
          else
          {
            throw new VCExprEvaluationException();
          }
        }
      }

      return dict.Count > 0 ? dict : null;
    }

    Dictionary<string, object> GetArrayFromArrayExpr(SExpr resp)
    {
      var dict = new Dictionary<string, object>();
      var curr = resp;
      while (curr != null)
      {
        if (curr.Name == "store")
        {
          var ary = curr.Arguments[0];
          var indices = curr.Arguments.Skip(1).Take(curr.ArgCount - 2).Select(ParseValueFromProver).ToArray();
          var val = curr.Arguments[curr.ArgCount - 1];
          dict.Add(String.Join(",", indices), ParseValueFromProver(val));
          curr = ary;
        }
        else if (curr.Name == "" && curr.ArgCount == 2 && curr.Arguments[0].Name == "as")
        {
          var val = curr.Arguments[1];
          dict.Add("*", ParseValueFromProver(val));
          curr = null;
        }
        else
        {
          return null;
        }
      }

      return dict.Count > 0 ? dict : null;
    }

    public override object Evaluate(VCExpr expr)
    {
      string vcString = VCExpr2String(expr, 1);
      SendThisVC("(get-value (" + vcString + "))");
      var resp = Process.GetProverResponse();
      if (resp == null) throw new VCExprEvaluationException();
      if (!(resp.Name == "" && resp.ArgCount == 1)) throw new VCExprEvaluationException();
      resp = resp.Arguments[0];
      if (resp.Name == "")
      {
        // evaluating an expression
        if (resp.ArgCount == 2)
          resp = resp.Arguments[1];
        else
          throw new VCExprEvaluationException();
      }
      else
      {
        // evaluating a variable
        if (resp.ArgCount == 1)
          resp = resp.Arguments[0];
        else
          throw new VCExprEvaluationException();
      }

      if (resp.Name == "-" && resp.ArgCount == 1) // negative int
        return Microsoft.BaseTypes.BigNum.FromString("-" + resp.Arguments[0].Name);
      if (resp.Name == "_" && resp.ArgCount == 2 && resp.Arguments[0].Name.StartsWith("bv")) // bitvector
        return new BvConst(Microsoft.BaseTypes.BigNum.FromString(resp.Arguments[0].Name.Substring("bv".Length)),
          int.Parse(resp.Arguments[1].Name));
      if (resp.Name == "fp" && resp.ArgCount == 3)
      {
        Func<SExpr, BigInteger> getBvVal = e => BigInteger.Parse(e.Arguments[0].Name.Substring("bv".Length));
        Func<SExpr, int> getBvSize = e => int.Parse(e.Arguments[1].ToString());
        bool isNeg = getBvVal(resp.Arguments[0]).IsOne;
        var expExpr = resp.Arguments[1];
        var sigExpr = resp.Arguments[2];
        BigInteger exp = getBvVal(expExpr);
        int expSize = getBvSize(expExpr);
        BigInteger sig = getBvVal(sigExpr);
        int sigSize = getBvSize(sigExpr) + 1;
        return new BaseTypes.BigFloat(isNeg, sig, exp, sigSize, expSize);
      }

      if (resp.Name == "_" && resp.ArgCount == 3)
      {
        String specialValue = resp.Arguments[0].ToString();
        int expSize = int.Parse(resp.Arguments[1].ToString());
        int sigSize = int.Parse(resp.Arguments[2].ToString());
        return new BaseTypes.BigFloat(specialValue, sigSize, expSize);
      }

      var ary = GetArrayFromProverResponse(resp);
      if (ary != null)
        return ary;
      if (resp.ArgCount != 0)
        throw new VCExprEvaluationException();
      if (expr.Type.Equals(Boogie.Type.Bool))
        return bool.Parse(resp.Name);
      else if (expr.Type.Equals(Boogie.Type.Int))
        return Microsoft.BaseTypes.BigNum.FromString(resp.Name);
      else
        return resp.Name;
    }

    /// <summary>
    /// Extra state for ApiChecker (used by stratifiedInlining)
    /// </summary>
    static int nameCounter = 0;

    public override Outcome CheckAssumptions(List<VCExpr> assumptions, out List<int> unsatCore, ErrorHandler handler)
    {
      unsatCore = new List<int>();

      Push();
      // Name the assumptions
      var nameToAssumption = new Dictionary<string, int>();
      int i = 0;
      foreach (var vc in assumptions)
      {
        var name = "a" + nameCounter.ToString();
        nameCounter++;
        nameToAssumption.Add(name, i);

        string vcString = VCExpr2String(vc, 1);
        AssertAxioms();
        SendThisVC(string.Format("(assert (! {0} :named {1}))", vcString, name));
        i++;
      }

      Check();

      var outcome = CheckOutcomeCore(handler);

      if (outcome != Outcome.Valid)
      {
        Pop();
        return outcome;
      }

      Contract.Assert(usingUnsatCore, "SMTLib prover not setup for computing unsat cores");
      SendThisVC("(get-unsat-core)");
      var resp = Process.GetProverResponse();
      unsatCore = new List<int>();
      if (resp.Name != "") unsatCore.Add(nameToAssumption[resp.Name]);
      foreach (var s in resp.Arguments) unsatCore.Add(nameToAssumption[s.Name]);

      FlushLogFile();
      Pop();
      return outcome;
    }

    public override void Push()
    {
      SendThisVC("(push 1)");
      DeclCollector.Push();
    }

    public override Outcome CheckAssumptions(List<VCExpr> hardAssumptions, List<VCExpr> softAssumptions,
      out List<int> unsatisfiedSoftAssumptions, ErrorHandler handler)
    {
      unsatisfiedSoftAssumptions = new List<int>();

      // First, convert both hard and soft assumptions to SMTLIB strings
      List<string> hardAssumptionStrings = new List<string>();
      foreach (var a in hardAssumptions)
      {
        hardAssumptionStrings.Add(VCExpr2String(a, 1));
      }

      List<string> currAssumptionStrings = new List<string>();
      foreach (var a in softAssumptions)
      {
        currAssumptionStrings.Add(VCExpr2String(a, 1));
      }

      Push();
      AssertAxioms();
      foreach (var a in hardAssumptionStrings)
      {
        SendThisVC("(assert " + a + ")");
      }

      Check();
      Outcome outcome = GetResponse();
      if (outcome != Outcome.Invalid)
      {
        Pop();
        return outcome;
      }

      int k = 0;
      List<string> relaxVars = new List<string>();
      while (true)
      {
        Push();
        foreach (var a in currAssumptionStrings)
        {
          SendThisVC("(assert " + a + ")");
        }

        Check();
        outcome = CheckOutcomeCore(handler);
        if (outcome != Outcome.Valid)
          break;
        Pop();
        string relaxVar = "relax_" + k;
        relaxVars.Add(relaxVar);
        SendThisVC("(declare-fun " + relaxVar + " () Int)");
        List<string> nextAssumptionStrings = new List<string>();
        for (int i = 0; i < currAssumptionStrings.Count; i++)
        {
          string constraint = "(= " + relaxVar + " " + i + ")";
          nextAssumptionStrings.Add("(or " + currAssumptionStrings[i] + " " + constraint + ")");
        }

        currAssumptionStrings = nextAssumptionStrings;
        k++;
      }

      if (outcome == Outcome.Invalid)
      {
        foreach (var relaxVar in relaxVars)
        {
          SendThisVC("(get-value (" + relaxVar + "))");
          FlushLogFile();
          var resp = Process.GetProverResponse();
          if (resp == null) break;
          if (!(resp.Name == "" && resp.ArgCount == 1)) break;
          resp = resp.Arguments[0];
          if (!(resp.Name != "" && resp.ArgCount == 1)) break;
          resp = resp.Arguments[0];
          if (resp.ArgCount != 0)
            break;
          int v;
          if (int.TryParse(resp.Name, out v))
            unsatisfiedSoftAssumptions.Add(v);
          else
            break;
        }

        Pop();
      }

      Pop();
      return outcome;
    }
  }
  
  public class SMTLibProverContext : DeclFreeProverContext
  {
    internal SMTLibProcessTheoremProver parent;
    
    public readonly HashSet<DatatypeTypeCtorDecl> KnownDatatypes = new HashSet<DatatypeTypeCtorDecl>();
    
    public readonly Dictionary<Function, VCExprNAry> DefinedFunctions = new Dictionary<Function, VCExprNAry>();

    public SMTLibProverContext(VCExpressionGenerator gen,
      VCGenerationOptions genOptions)
      : base(gen, genOptions)
    {
    }

    protected SMTLibProverContext(SMTLibProverContext par)
      : base(par)
    {
    }

    public override object Clone()
    {
      return new SMTLibProverContext(this);
    }

    public override string Lookup(VCExprVar var)
    {
      VCExprVar v = parent.AxBuilder?.TryTyped2Untyped(var);
      if (v != null)
      {
        var = v;
      }

      return parent.Namer.Lookup(var);
    }

    public override void DeclareFunction(Function f, string attributes)
    {
      if (f.DefinitionBody != null)
      {
        DefinedFunctions.Add(f, (VCExprNAry) translator.Translate(f.DefinitionBody));
      }

      base.DeclareFunction(f, attributes);
    }

    public override void DeclareType(TypeCtorDecl t, string attributes)
    {
      if (t is DatatypeTypeCtorDecl datatypeTypeCtorDecl)
      {
        if (datatypeTypeCtorDecl.Arity > 0)
        {
          throw new ProverException("Polymorphic datatypes are not supported");
        }
        KnownDatatypes.Add(datatypeTypeCtorDecl);
      }
      base.DeclareType(t, attributes);
    }

    // Return the datatype of the given name if there is one, null otherwise.
    public DatatypeTypeCtorDecl LookupDatatype(string name)
    {
      foreach (var datatype in KnownDatatypes)
      {
        if (name == datatype.ToString())
        {
          return datatype;
        }
      }

      return null;
    }
  }

  public class Factory : ProverFactory
  {
    public override object SpawnProver(ProverOptions options, object ctxt)
    {
      //Contract.Requires(ctxt != null);
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      return this.SpawnProver(options,
        cce.NonNull((SMTLibProverContext) ctxt).ExprGen,
        cce.NonNull((SMTLibProverContext) ctxt));
    }

    public override object NewProverContext(ProverOptions options)
    {
      //Contract.Requires(options != null);
      Contract.Ensures(Contract.Result<object>() != null);

      VCExpressionGenerator gen = new VCExpressionGenerator();
      List<string> /*!>!*/
        proverCommands = new List<string /*!*/>();
      proverCommands.Add("smtlib");
      var opts = (SMTLibProverOptions) options;
      if (opts.Solver == SolverKind.Z3)
        proverCommands.Add("z3");
      else
        proverCommands.Add("external");
      VCGenerationOptions genOptions = new VCGenerationOptions(proverCommands);
      return new SMTLibProverContext(gen, genOptions);
    }

    public override ProverOptions BlankProverOptions()
    {
      return new SMTLibProverOptions();
    }

    protected virtual SMTLibProcessTheoremProver SpawnProver(ProverOptions options,
      VCExpressionGenerator gen,
      SMTLibProverContext ctx)
    {
      Contract.Requires(options != null);
      Contract.Requires(gen != null);
      Contract.Requires(ctx != null);
      Contract.Ensures(Contract.Result<SMTLibProcessTheoremProver>() != null);
      return new SMTLibProcessTheoremProver(options, gen, ctx);
    }
  }
}