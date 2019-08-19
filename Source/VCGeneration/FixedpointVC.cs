//-----------------------------------------------------------------------------
//
// Copyright (C) 2012 Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;


using Term = Microsoft.Boogie.VCExprAST.VCExpr;
using FuncDecl = Microsoft.Boogie.VCExprAST.VCExprOp;
using Sort = Microsoft.Boogie.Type;
using Microsoft.Boogie.ExprExtensions;


namespace Microsoft.Boogie
{
    public class FixedpointVC : VC.VCGen
    {

        public class AnnotationInfo
        {
            public enum AnnotationType { LoopInvariant, ProcedureSummary };
            public string filename;
            public int lineno;
            public string[] argnames;
            public AnnotationType type;
        };

        static bool NoLabels = false;
        
        // options
        bool largeblock = false;

        public bool SetOption(string option, string value)
        {
            if (option == "LargeBlock")
            {
                largeblock = true;
                return true;
            }
            return false;
        }

        Context ctx;
        RPFP rpfp;
        // Program program;
        Microsoft.Boogie.ProverContext boogieContext;
        Microsoft.Boogie.VCExpressionGenerator gen;
        public readonly static string recordProcName = "boogie_si_record"; // TODO: this really needed?
        private Dictionary<string, StratifiedInliningInfo> implName2StratifiedInliningInfo
            = new Dictionary<string, StratifiedInliningInfo>();
        Checker checker;
        // Microsoft.Boogie.Z3.Z3InstanceOptions options = new Microsoft.Boogie.Z3.Z3InstanceOptions(); // TODO: what?
        LineariserOptions linOptions;
        Dictionary<FuncDecl, StratifiedInliningInfo> relationToProc = new Dictionary<FuncDecl, StratifiedInliningInfo>();
        Dictionary<string, Term> labels = new Dictionary<string, Term> ();
        List<Term> DualityVCs = new List<Term>();
        Dictionary<string, bool> summaries = new Dictionary<string, bool>();
        Dictionary<Block, List<Block>> edgesCut = new Dictionary<Block, List<Block>>();
        string main_proc_name = "main";
        Dictionary<string, int> extraRecBound = null;
        

        public enum Mode { Corral, OldCorral, Boogie};
        public enum AnnotationStyle { Flat, Procedure, Call };

        Mode mode;
        AnnotationStyle style;

        private static Checker old_checker = null;

        public static void CleanUp()
        {
            if (old_checker != null)
            {
                old_checker.Close();
                old_checker = null;
            }
        }

        public FixedpointVC( Program _program, string/*?*/ logFilePath, bool appendLogFile, List<Checker> checkers, Dictionary<string,int> _extraRecBound = null)
            : base(_program, logFilePath, appendLogFile, checkers) 
        {
            switch (CommandLineOptions.Clo.FixedPointMode)
            {
                case CommandLineOptions.FixedPointInferenceMode.Corral:
                    mode = Mode.Corral;
                    style = AnnotationStyle.Procedure;
                    break;
                case CommandLineOptions.FixedPointInferenceMode.OldCorral:
                    mode = Mode.OldCorral;
                    style = AnnotationStyle.Procedure;
                    break;
                case CommandLineOptions.FixedPointInferenceMode.Flat:
                    mode = Mode.Boogie;
                    style = AnnotationStyle.Flat;
                    break;
                case CommandLineOptions.FixedPointInferenceMode.Procedure:
                    mode = Mode.Boogie;
                    style = AnnotationStyle.Procedure;
                    break;
                case CommandLineOptions.FixedPointInferenceMode.Call:
                    mode = Mode.Boogie;
                    style = AnnotationStyle.Call;
                    break;
            }
            ctx = new Context(); // TODO is this right?
            rpfp = new RPFP(RPFP.CreateLogicSolver(ctx));
            program = _program;
            gen = ctx;
            if(old_checker == null)
                checker = new Checker(this, program, logFilePath, appendLogFile, CommandLineOptions.Clo.ProverKillTime, CommandLineOptions.Clo.Resourcelimit, null);
            else {
                checker = old_checker;
                checker.RetargetWithoutReset(program,checker.TheoremProver.Context);
            }
            old_checker = checker;
            boogieContext = checker.TheoremProver.Context;
            linOptions = null; //  new Microsoft.Boogie.Z3.Z3LineariserOptions(false, options, new List<VCExprVar>());
            extraRecBound = _extraRecBound;
        }

        Dictionary<string, AnnotationInfo> annotationInfo = new Dictionary<string, AnnotationInfo>();
        
        public void AnnotateLoops(Implementation impl, ProverContext ctxt)
        {
            Contract.Requires(impl != null);

            CurrentLocalVariables = impl.LocVars;
            variable2SequenceNumber = new Dictionary<Variable, int>();
            incarnationOriginMap = new Dictionary<Incarnation, Absy>();

            ResetPredecessors(impl.Blocks);

            #region Create the graph by adding the source node and each edge
            GraphUtil.Graph<Block> g = Program.GraphFromImpl(impl);
            #endregion

            //Graph<Block> g = program.ProcessLoops(impl);

            g.ComputeLoops(); // this is the call that does all of the processing
            if (!g.Reducible)
            {
                throw new System.Exception("Irreducible flow graphs are unsupported.");
            }

            #region add a symbolic annoation to every loop head
            foreach (Block header in cce.NonNull(g.Headers))
                AnnotateBlock(impl, ctxt, header);
            #endregion
        }

        private void AnnotateCallSites(Implementation impl, ProverContext ctxt, Dictionary<string, bool> impls){
            foreach (var b in impl.Blocks)
            {
                foreach (var cmd in b.Cmds)
                {
                    if (cmd is CallCmd)
                    {
                        string name = (cmd as CallCmd).callee;
                        if(impls.ContainsKey(name))
                            goto annotate;
                    }
                }
                continue;
            annotate:
                AnnotateBlock(impl, ctxt, b);
            }
        }


        private void AnnotateBlock(Implementation impl, ProverContext ctxt, Block header)
        {
            Contract.Assert(header != null);
            
            string name = impl.Name + "_" + header.Label + "_invar";
            if (annotationInfo.ContainsKey(name))
                return;

            // collect the variables needed in the invariant
            List<Expr> exprs = new List<Expr>();
            List<Variable> vars = new List<Variable>();
            List<string> names = new List<string>();

            if (style == AnnotationStyle.Flat)
            {
                // in flat mode, all live globals should be in live set
#if false
                foreach (Variable v in program.GlobalVariables)
                {
                    vars.Add(v);
                    names.Add(v.ToString());
                    exprs.Add(new IdentifierExpr(Token.NoToken, v));
                }
#endif
                foreach (Variable v in /* impl.LocVars */ header.liveVarsBefore)
                {
                    if (!(v is BoundVariable))
                    {
                        vars.Add(v);
                        names.Add(v.ToString());
                        exprs.Add(new IdentifierExpr(Token.NoToken, v));
                    }
                }
            }
            else
            {
                foreach (Variable v in program.GlobalVariables)
                {
                    vars.Add(v);
                    names.Add("@old_" + v.ToString());
                    exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                }
                foreach (IdentifierExpr ie in impl.Proc.Modifies)
                {
                    if (ie.Decl == null)
                        continue;
                    vars.Add(ie.Decl);
                    names.Add(ie.Decl.ToString());
                    exprs.Add(ie);
                }
                foreach (Variable v in impl.Proc.InParams)
                {
                    Contract.Assert(v != null);
                    vars.Add(v);
                    names.Add("@old_" + v.ToString());
                    exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                }
                foreach (Variable v in impl.LocVars)
                {
                    vars.Add(v);
                    names.Add(v.ToString()); 
                    exprs.Add(new IdentifierExpr(Token.NoToken, v));
                }
            }
            
            TypedIdent ti = new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool);
            Contract.Assert(ti != null);
            Formal returnVar = new Formal(Token.NoToken, ti, false);
            Contract.Assert(returnVar != null);
            var function = new Function(Token.NoToken, name, vars, returnVar);
            ctxt.DeclareFunction(function, "");

            Expr invarExpr = new NAryExpr(Token.NoToken, new FunctionCall(function), exprs);
            var invarAssertion = new AssertCmd(Token.NoToken, invarExpr);
            List<Cmd> newCmds = new List<Cmd>();
            newCmds.Add(invarAssertion);

            // make a record in annotationInfo;
            var info = new AnnotationInfo();
            info.filename = header.tok.filename;
            info.lineno = header.Line;
            info.argnames = names.ToArray();
            info.type = AnnotationInfo.AnnotationType.LoopInvariant;
            annotationInfo.Add(name, info);
            // get file and line info from havoc, if there is...
            if (header.Cmds.Count > 0)
            {
                PredicateCmd bif = header.Cmds[0] as PredicateCmd;
                if (bif != null)
                {
                    string foo = QKeyValue.FindStringAttribute(bif.Attributes, "sourcefile");
                    if (foo != null)
                        info.filename = foo;
                    int bar = QKeyValue.FindIntAttribute(bif.Attributes, "sourceline", -1);
                    if (bar != -1)
                        info.lineno = bar;
                }
            }
            var thing = header;
            foreach (Cmd c in header.Cmds)
            {
                newCmds.Add(c);
            }
            header.Cmds = newCmds;
        }

#if true
        public void AnnotateProcRequires(Procedure proc, Implementation impl, ProverContext ctxt)
        {
            Contract.Requires(impl != null);

            CurrentLocalVariables = impl.LocVars;

            // collect the variables needed in the invariant
            List<Expr> exprs = new List<Expr>();
            List<Variable> vars = new List<Variable>();
            List<string> names = new List<string>();

            foreach (Variable v in program.GlobalVariables)
            {
                vars.Add(v);
                exprs.Add(new IdentifierExpr(Token.NoToken, v));
                names.Add(v.Name);
            }
            foreach (Variable v in proc.InParams)
            {
                Contract.Assert(v != null);
                vars.Add(v);
                exprs.Add(new IdentifierExpr(Token.NoToken, v));
                names.Add(v.Name);
            }
            string name = impl.Name + "_precond";
            TypedIdent ti = new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool);
            Contract.Assert(ti != null);
            Formal returnVar = new Formal(Token.NoToken, ti, false);
            Contract.Assert(returnVar != null);
            var function = new Function(Token.NoToken, name, vars, returnVar);
            ctxt.DeclareFunction(function, "");

            Expr invarExpr = new NAryExpr(Token.NoToken, new FunctionCall(function), exprs);

            proc.Requires.Add(new Requires(Token.NoToken, false, invarExpr, "", null));
            
            var info = new AnnotationInfo();
            info.filename = proc.tok.filename;
            info.lineno = proc.Line;
            info.argnames = names.ToArray();
            info.type = AnnotationInfo.AnnotationType.LoopInvariant;
            annotationInfo.Add(name, info);
        }

        public void AnnotateProcEnsures(Procedure proc, Implementation impl, ProverContext ctxt)
        {
            Contract.Requires(impl != null);

            CurrentLocalVariables = impl.LocVars;

            // collect the variables needed in the invariant
            List<Expr> exprs = new List<Expr>();
            List<Variable> vars = new List<Variable>();
            List<string> names = new List<string>();

                foreach (Variable v in program.GlobalVariables)
                {
                    vars.Add(v);
                    exprs.Add(new OldExpr(Token.NoToken,new IdentifierExpr(Token.NoToken, v)));
                    names.Add(v.Name);
                }
                foreach (Variable v in proc.InParams)
                {
                    Contract.Assert(v != null);
                    vars.Add(v);
                    exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                    names.Add(v.Name);
                }
                foreach (IdentifierExpr ie in proc.Modifies)
                        {
                            if (ie.Decl == null)
                                continue;
                            vars.Add(ie.Decl);
                            exprs.Add(ie);
                            names.Add(ie.Decl.Name + "_out");
                        }
                foreach (Variable v in proc.OutParams)
                {
                            Contract.Assert(v != null);
                            vars.Add(v);
                            exprs.Add(new IdentifierExpr(Token.NoToken, v));
                            names.Add(v.Name);
                }
                string name = impl.Name + "_summary";
                summaries.Add(name, true);
                TypedIdent ti = new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool);
                Contract.Assert(ti != null);
                Formal returnVar = new Formal(Token.NoToken, ti, false);
                Contract.Assert(returnVar != null);
                var function = new Function(Token.NoToken, name, vars, returnVar);
                ctxt.DeclareFunction(function, "");

                Expr invarExpr = new NAryExpr(Token.NoToken, new FunctionCall(function), exprs);
                
            proc.Ensures.Add(new Ensures(Token.NoToken, false, invarExpr, "", null));
            
            var info = new AnnotationInfo();
            info.filename = proc.tok.filename;
            info.lineno = proc.Line;
            info.argnames = names.ToArray();
            info.type = AnnotationInfo.AnnotationType.ProcedureSummary;
            annotationInfo.Add(name, info);
        }
#endif

        void MarkAllFunctionImplementationsInline()
        {
            foreach (var func in program.Functions)
            {
                if (func.Body == null && func.DefinitionAxiom != null)
                {
                    var def = func.DefinitionAxiom.Expr as QuantifierExpr;
                    var bod = def.Body as NAryExpr;
                    func.Body = bod.Args[1];
                    func.DefinitionAxiom = null;
                }
                if (func.Body != null)
                    if (func.FindExprAttribute("inline") == null)
                        func.AddAttribute("inline", Expr.Literal(100));
            }
        }

        void InlineAll()
        {
            foreach (var impl in program.Implementations)
            {
                impl.OriginalBlocks = impl.Blocks;
                impl.OriginalLocVars = impl.LocVars;
                if(impl.Name != main_proc_name)
                  if(impl.FindExprAttribute("inline") == null)
                    impl.AddAttribute("inline", Expr.Literal(100));
            }
            foreach (var impl in program.Implementations)
            {
                if (!impl.SkipVerification)
                {
                    Inliner.ProcessImplementation(program, impl);
                }
            }
            foreach (var impl in program.Implementations)
            {
                impl.OriginalBlocks = null;
                impl.OriginalLocVars = null;
            }
        }

        public class LazyInliningInfo
        {
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(impl != null);
                Contract.Invariant(function != null);
                Contract.Invariant(controlFlowVariable != null);
                Contract.Invariant(assertExpr != null);
                Contract.Invariant(cce.NonNullElements(interfaceVars));
                Contract.Invariant(incarnationOriginMap == null || cce.NonNullDictionaryAndValues(incarnationOriginMap));
            }

            public Implementation impl;
            public int uniqueId;
            public Function function;
            public Variable controlFlowVariable;
            public List<Variable> interfaceVars;
            public List<List<Variable>> interfaceVarCopies;
            public Expr assertExpr;
            public VCExpr vcexpr;
            public List<VCExprVar> privateVars;
            public Dictionary<Incarnation, Absy> incarnationOriginMap;
            public Hashtable /*Variable->Expr*/ exitIncarnationMap;
            public Hashtable /*GotoCmd->returnCmd*/ gotoCmdOrigins;
            public Dictionary<int, Absy> label2absy;
            public VC.ModelViewInfo mvInfo;

            public Dictionary<Block, VCExprVar> reachVars;
            public List<VCExprLetBinding> reachVarBindings;
            public Variable inputErrorVariable;
            public Variable outputErrorVariable;



            public LazyInliningInfo(Implementation impl, Program program, ProverContext ctxt, int uniqueId, GlobalVariable errorVariable)
            {
                Contract.Requires(impl != null);
                Contract.Requires(program != null);
                Procedure proc = cce.NonNull(impl.Proc);

                this.impl = impl;
                this.uniqueId = uniqueId;
                this.controlFlowVariable = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "cfc", Microsoft.Boogie.Type.Int));
                impl.LocVars.Add(controlFlowVariable);

                List<Variable> interfaceVars = new List<Variable>();
                Expr assertExpr = new LiteralExpr(Token.NoToken, true);
                Contract.Assert(assertExpr != null);
                // InParams must be obtained from impl and not proc
                foreach (Variable v in impl.InParams)
                {
                    Contract.Assert(v != null);
                    interfaceVars.Add(v);
                }
                // OutParams must be obtained from impl and not proc
                foreach (Variable v in impl.OutParams)
                {
                    Contract.Assert(v != null);
                    Constant c = new Constant(Token.NoToken,
                                              new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
                    interfaceVars.Add(c);
                    Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
                    assertExpr = Expr.And(assertExpr, eqExpr);
                }
                foreach (Variable v in program.GlobalVariables)
                {
                    Contract.Assert(v != null);
                    interfaceVars.Add(v);
                    if (v.Name == "error")
                        inputErrorVariable = v;
                }
                if (errorVariable != null)
                {
                    proc.Modifies.Add(new IdentifierExpr(Token.NoToken, errorVariable));
                }
                foreach (IdentifierExpr e in proc.Modifies)
                {
                    Contract.Assert(e != null);
                    if (e.Decl == null)
                        continue;
                    Variable v = e.Decl;
                    Constant c = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, impl.Name + "_" + v.Name, v.TypedIdent.Type));
                    interfaceVars.Add(c);
                    if (v.Name == "error")
                    {
                        outputErrorVariable = c;
                        continue;
                    }
                    Expr eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, c), new IdentifierExpr(Token.NoToken, v));
                    assertExpr = Expr.And(assertExpr, eqExpr);
                }

                this.interfaceVars = interfaceVars;
                this.assertExpr = Expr.Not(assertExpr);
                List<Variable> functionInterfaceVars = new List<Variable>();
                foreach (Variable v in interfaceVars)
                {
                    Contract.Assert(v != null);
                    functionInterfaceVars.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type), true));
                }
                TypedIdent ti = new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool);
                Contract.Assert(ti != null);
                Formal returnVar = new Formal(Token.NoToken, ti, false);
                Contract.Assert(returnVar != null);
                this.function = new Function(Token.NoToken, proc.Name, functionInterfaceVars, returnVar);
                ctxt.DeclareFunction(this.function, "");

                interfaceVarCopies = new List<List<Variable>>();
                int temp = 0;
                for (int i = 0; i < /* CommandLineOptions.Clo.ProcedureCopyBound */ 0; i++)
                {
                    interfaceVarCopies.Add(new List<Variable>());
                    foreach (Variable v in interfaceVars)
                    {
                        Constant constant = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, v.Name + temp++, v.TypedIdent.Type));
                        interfaceVarCopies[i].Add(constant);
                        //program.AddTopLevelDeclaration(constant);
                    }
                }
            }
        }

        public class StratifiedInliningInfo : LazyInliningInfo
        {
            [ContractInvariantMethod]
            void ObjectInvariant()
            {
                Contract.Invariant(cce.NonNullElements(privateVars));
                Contract.Invariant(cce.NonNullElements(interfaceExprVars));
                Contract.Invariant(cce.NonNullElements(interfaceExprVars));
            }

            // public StratifiedVCGenBase vcgen;
            //public Implementation impl;
            //public Program program;
            //public ProverContext ctxt;
            //public int uniqueid;
            //public Function function;
            //public Variable controlFlowVariable;
            //public Expr assertExpr;
            //public VCExpr vcexpr;
            //public List<VCExprVar> interfaceExprVars;
            //public List<VCExprVar> privateExprVars;
            //public Dictionary<int, Absy> label2absy;
            //public VC.ModelViewInfo mvInfo;
            //public Dictionary<Block, List<CallSite>> callSites;
            //public Dictionary<Block, List<CallSite>> recordProcCallSites;
            //public IEnumerable<Block> sortedBlocks;
            //public bool initialized { get; private set; }


            public List<VCExprVar> interfaceExprVars; 
            // public List<VCExprVar> privateVars;
            public VCExpr funcExpr;
            public VCExpr falseExpr;
            public RPFP.Transformer F;
            public RPFP.Node node;
            public RPFP.Edge edge;
            public bool isMain = false;
            public Dictionary<Absy, string> label2absyInv;
            public ProverContext ctxt;
            public Hashtable/*<Block, LetVariable!>*/ blockVariables = new Hashtable/*<Block, LetVariable!!>*/();
            public List<VCExprLetBinding> bindings = new List<VCExprLetBinding>();
                
            public StratifiedInliningInfo(Implementation _impl, Program _program, ProverContext _ctxt, int _uniqueid)
            : base(_impl,_program,_ctxt,_uniqueid,null){
                Contract.Requires(_impl != null);
                Contract.Requires(_program != null);
                privateVars = new List<VCExprVar>();
                interfaceExprVars = new List<VCExprVar>();
                ctxt = _ctxt;
            }

        }

        protected override void addExitAssert(string implName, Block exitBlock)
        {
            if (implName2StratifiedInliningInfo != null
                && implName2StratifiedInliningInfo.ContainsKey(implName)
                && !implName2StratifiedInliningInfo[implName].isMain)
            {
                if (mode == Mode.Boogie) return;
                Expr assertExpr = implName2StratifiedInliningInfo[implName].assertExpr;
                Contract.Assert(assertExpr != null);
                exitBlock.Cmds.Add(new AssertCmd(Token.NoToken, assertExpr));
            }
        }

#if false
        protected override void storeIncarnationMaps(string implName, Hashtable exitIncarnationMap)
        {
            if (implName2StratifiedInliningInfo != null && implName2StratifiedInliningInfo.ContainsKey(implName))
            {
                StratifiedInliningInfo info = implName2StratifiedInliningInfo[implName];
                Contract.Assert(info != null);
                info.exitIncarnationMap = exitIncarnationMap;
                info.incarnationOriginMap = this.incarnationOriginMap;
            }
        }
#endif

        public void GenerateVCsForStratifiedInlining()
        {
            Contract.Requires(program != null);
            foreach (var impl in program.Implementations)
            {
                Contract.Assert(!impl.Name.StartsWith(recordProcName), "Not allowed to have an implementation for this guy");

                Procedure proc = cce.NonNull(impl.Proc);

                {
                    StratifiedInliningInfo info = new StratifiedInliningInfo(impl, program, boogieContext, QuantifierExpr.GetNextSkolemId());
                    implName2StratifiedInliningInfo[impl.Name] = info;
                    // We don't need controlFlowVariable for stratified Inlining
                    //impl.LocVars.Add(info.controlFlowVariable);
                    List<Expr> exprs = new List<Expr>();

                    if (mode != Mode.Boogie && QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint"))
                    {
                        proc.Ensures.Add(new Ensures(Token.NoToken, true, Microsoft.Boogie.Expr.False, "", null));
                        info.assertExpr = Microsoft.Boogie.Expr.False;
                        // info.isMain = true;
                    }
                    else if (mode == Mode.Corral || proc.FindExprAttribute("inline") != null || proc is LoopProcedure)
                    {
                        foreach (Variable v in proc.InParams)
                        {
                            Contract.Assert(v != null);
                            exprs.Add(new IdentifierExpr(Token.NoToken, v));
                        }
                        foreach (Variable v in proc.OutParams)
                        {
                            Contract.Assert(v != null);
                            exprs.Add(new IdentifierExpr(Token.NoToken, v));
                        }
                        foreach (Variable v in program.GlobalVariables)
                        {
                            Contract.Assert(v != null);
                            exprs.Add(new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                        }
                        foreach (IdentifierExpr ie in proc.Modifies)
                        {
                            Contract.Assert(ie != null);
                            if (ie.Decl == null)
                                continue;
                            exprs.Add(ie);
                        }
                        Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(info.function), exprs);
#if true
                        if(mode == Mode.Corral || mode == Mode.OldCorral)
                            proc.Ensures.Add(new Ensures(Token.NoToken, true, freePostExpr, "", new QKeyValue(Token.NoToken, "si_fcall", new List<object>(), null)));
#endif
                    }
                    else // not marked "inline" must be main
                    {
                        Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(info.function), exprs);
                        info.isMain = true;
                    }
                }
            }

            if (mode == Mode.Boogie) return;

            foreach (var proc in program.Procedures)
            {
                if (!proc.Name.StartsWith(recordProcName)) continue;
                Contract.Assert(proc.InParams.Count == 1);

                // Make a new function
                TypedIdent ti = new TypedIdent(Token.NoToken, "", Microsoft.Boogie.Type.Bool);
                Contract.Assert(ti != null);
                Formal returnVar = new Formal(Token.NoToken, ti, false);
                Contract.Assert(returnVar != null);

                // Get record type
                var argtype = proc.InParams[0].TypedIdent.Type;

                var ins = new List<Variable>();
                ins.Add(new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "x", argtype), true));

                var recordFunc = new Function(Token.NoToken, proc.Name, ins, returnVar);
                boogieContext.DeclareFunction(recordFunc, "");

                var exprs = new List<Expr>();
                exprs.Add(new IdentifierExpr(Token.NoToken, proc.InParams[0]));

                Expr freePostExpr = new NAryExpr(Token.NoToken, new FunctionCall(recordFunc), exprs);
                proc.Ensures.Add(new Ensures(true, freePostExpr));
            }
        }
		
		private void FixedPointToSpecs(){
			
			if(mode != Mode.Corral || CommandLineOptions.Clo.PrintFixedPoint == null)
				return; // not implemented for other annotation modes yet
			
            var twr = new TokenTextWriter(CommandLineOptions.Clo.PrintFixedPoint, /*pretty=*/ false);
			Dictionary<string, RPFP.Node> pmap = new Dictionary<string,RPFP.Node> ();

			foreach (var node in rpfp.nodes)
				pmap.Add ((node.Name as VCExprBoogieFunctionOp).Func.Name, node);
			
			foreach (var impl in program.Implementations)
            {
                Contract.Assert(!impl.Name.StartsWith(recordProcName), "Not allowed to have an implementation for this guy");

                Procedure proc = cce.NonNull(impl.Proc);

                {
                    StratifiedInliningInfo info = new StratifiedInliningInfo(impl, program, boogieContext, QuantifierExpr.GetNextSkolemId());
                    implName2StratifiedInliningInfo[impl.Name] = info;
                    // We don't need controlFlowVariable for stratified Inlining
                    //impl.LocVars.Add(info.controlFlowVariable);
                    List<Expr> exprs = new List<Expr>();

                    {
                        if (pmap.ContainsKey(impl.Name))
                        {
                            RPFP.Node node = pmap[impl.Name];
                            var annot = node.Annotation;
                            EmitProcSpec(twr, proc, info, annot);
                        }
                    }
                }
            }
			twr.Close ();
		}

        private void EmitProcSpec(TokenTextWriter twr, Procedure proc, StratifiedInliningInfo info, RPFP.Transformer annot)
        {
            // last ensures clause will be the symbolic one
            if (!info.isMain)
            {
                var ens = proc.Ensures[proc.Ensures.Count - 1];
                if (ens.Condition != Expr.False) // this is main
                {
                    var postExpr = ens.Condition as NAryExpr;
                    var args = postExpr.Args;

                    var ind = annot.IndParams;
                    var bound = new Dictionary<VCExpr, Expr>();
                    for (int i = 0; i < args.Count; i++)
                    {
                        bound[ind[i]] = args[i];
                    }
                    var new_ens_cond = VCExprToExpr(annot.Formula, bound);
                    if (new_ens_cond != Expr.True)
                    {
                        var new_ens = new Ensures(false, new_ens_cond);
                        var enslist = new List<Ensures>();
                        enslist.Add(new_ens);
                        var new_proc = new Procedure(proc.tok, proc.Name, proc.TypeParameters, proc.InParams,
                                                     proc.OutParams, new List<Requires>(), new List<IdentifierExpr>(), enslist);
                        new_proc.Emit(twr, 0);
                    }
                }
            }
        }

        static int ConjectureFileCounter = 0;

        private void ConjecturesToSpecs()
        {

            if (mode != Mode.Corral || CommandLineOptions.Clo.PrintConjectures == null)
                return; // not implemented for other annotation modes yet

            var twr = new TokenTextWriter(CommandLineOptions.Clo.PrintConjectures + "." + ConjectureFileCounter.ToString(), /*pretty=*/ false);
            ConjectureFileCounter++;

            foreach (var c in rpfp.conjectures)
            {
                var name = c.node.Name.GetDeclName();
                if (implName2StratifiedInliningInfo.ContainsKey(name))
                {
                    StratifiedInliningInfo info = implName2StratifiedInliningInfo[c.node.Name.GetDeclName()];
                    Implementation impl = info.impl;
                    Procedure proc = impl.Proc;
                    EmitProcSpec(twr, proc, info, c.bound);
                }
            }

            twr.Close ();     
        }

        private Term ExtractSmallerVCsRec(TermDict< Term> memo, Term t, List<Term> small, Term lbl = null)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            var kind = t.GetKind();
            if (kind == TermKind.App)
            {
                var f = t.GetAppDecl();
                if (f.GetKind() == DeclKind.Implies){
                    var lhs = t.GetAppArgs()[0];
                    if(lhs.GetKind() == TermKind.App){
                        var r = lhs.GetAppDecl();
                        if (r.GetKind() == DeclKind.And)
                        {
                            Term q = t.GetAppArgs()[1];
                            var lhsargs = lhs.GetAppArgs();
                            for (int i = lhsargs.Length-1; i >= 0; --i)
                            {
                                q = ctx.MkImplies(lhsargs[i], q);
                            }
                            res = ExtractSmallerVCsRec(memo, q, small,lbl);
                            goto done;
                        }
                        if (r.GetKind() == DeclKind.Label)
                        {
                            var arg = lhs; 
                            arg = lhs.GetAppArgs()[0];
                            if (!(arg.GetKind() == TermKind.App && arg.GetAppDecl().GetKind() == DeclKind.Uninterpreted))
                                goto normal;
                            if (!(annotationInfo.ContainsKey(arg.GetAppDecl().GetDeclName()) && annotationInfo[arg.GetAppDecl().GetDeclName()].type == AnnotationInfo.AnnotationType.LoopInvariant))
                                goto normal;
                            var sm = ctx.MkImplies(lhs, ExtractSmallerVCsRec(memo, t.GetAppArgs()[1], small));
                            if (lbl != null)
                                sm = ctx.MkImplies(lbl, sm);
                            small.Add(sm);
                            res = ctx.MkTrue();
                            goto done;
                        }
                        if (r.GetKind() == DeclKind.Uninterpreted)
                        {
                            var arg = lhs;
                            if (!(annotationInfo.ContainsKey(arg.GetAppDecl().GetDeclName()) && annotationInfo[arg.GetAppDecl().GetDeclName()].type == AnnotationInfo.AnnotationType.LoopInvariant))
                                goto normal;
                            var sm = ctx.MkImplies(lhs,ExtractSmallerVCsRec(memo,t.GetAppArgs()[1],small));
                            if (lbl != null)
                                sm = ctx.MkImplies(lbl, sm); 
                            small.Add(sm);
                            res = ctx.MkTrue();
                            goto done;
                        }
                    }
                normal:
                    Term newlbl = null;
                    if (lhs.IsLabel() && lhs.GetAppArgs()[0] == ctx.MkTrue())
                        newlbl = lhs;
                    res = ctx.MkImplies(lhs,ExtractSmallerVCsRec(memo,t.GetAppArgs()[1],small,newlbl));
                }
                else if (f.GetKind() == DeclKind.And)
                {
                    res = ctx.MkApp(f,t.GetAppArgs().Select(x => ExtractSmallerVCsRec(memo, x, small)).ToArray());
                }
                else
                    res = t;
            }
            else
                res = t;
            done:
            memo.Add(t, res);
            return res;
        }

        private void ExtractSmallerVCs(Term t, List<Term> small){
            TermDict< Term> memo = new TermDict< Term>();
            Term top = ExtractSmallerVCsRec(memo, t, small);
            small.Add(top);
        }

        private Dictionary<FuncDecl, int> goalNumbering = new Dictionary<FuncDecl, int>();

        private Term NormalizeGoal(Term goal, FuncDecl label)
        {
            var f = goal.GetAppDecl();
            var args = goal.GetAppArgs();
            int number;
            if (!goalNumbering.TryGetValue(f, out number))
            {
                number = goalNumbering.Count;
                goalNumbering.Add(f, number);
            }
            Term[] tvars = new Term[args.Length];
            Term[] eqns = new Term[args.Length];
            AnnotationInfo info = null;
            annotationInfo.TryGetValue(f.GetDeclName(), out info);
            for (int i = 0; i < args.Length; i++)
            {
                string pname = (info == null) ? i.ToString() : info.argnames[i];
                tvars[i] = ctx.MkConst("@a" + number.ToString() + "_" + pname, args[i].GetSort());
                eqns[i] = ctx.MkEq(tvars[i], args[i]);
            }
            return ctx.MkImplies(ctx.MkAnd(eqns), ctx.MkApp(label, ctx.MkApp(f, tvars)));
        }

        private Term MergeGoalsRec(TermDict< Term> memo, Term t)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            var kind = t.GetKind();
            if (kind == TermKind.App)
            {
                var f = t.GetAppDecl();
                var args = t.GetAppArgs();
                if (f.GetKind() == DeclKind.Implies)
                {
                    res = ctx.MkImplies(args[0], MergeGoalsRec(memo, args[1]));
                    goto done;
                }
                else if (f.GetKind() == DeclKind.And)
                {
                    args = args.Select(x => MergeGoalsRec(memo, x)).ToArray();
                    res = ctx.MkApp(f, args);
                    goto done;
                }
                else if (f.GetKind() == DeclKind.Label)
                {
                    var arg = t.GetAppArgs()[0];
                    var r = arg.GetAppDecl();
                    if (r.GetKind() == DeclKind.Uninterpreted)
                    {
                        res = NormalizeGoal(arg, f);
                        goto done;
                    }
                }
            }
            res = t;
        done:
            memo.Add(t, res);
            return res;
        }

        private Term MergeGoals(Term t)
        {
            TermDict< Term> memo = new TermDict< Term>();
            return MergeGoalsRec(memo, t);
        }

        private Term CollectGoalsRec(TermDict< Term> memo, Term t, List<Term> goals, List<Term> cruft)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            var kind = t.GetKind();
            if (kind == TermKind.App)
            {
                var f = t.GetAppDecl();
                if (f.GetKind() == DeclKind.Implies)
                {
                    CollectGoalsRec(memo, t.GetAppArgs()[1], goals, cruft);
                    goto done;
                }
                else if (f.GetKind() == DeclKind.And)
                {
                    foreach (var arg in t.GetAppArgs())
                    {
                        CollectGoalsRec(memo, arg, goals, cruft);
                    }
                    goto done;
                }
                else if (f.GetKind() == DeclKind.Label)
                {
                    var arg = t.GetAppArgs()[0];
                    if (arg.GetKind() == TermKind.App && arg.GetAppDecl().GetKind() == DeclKind.Uninterpreted)
                    {
                        var r = arg.GetAppDecl();
                        if (memo.TryGetValue(arg, out res))
                            goto done;
                        if (!annotationInfo.ContainsKey(r.GetDeclName()) && !arg.GetAppDecl().GetDeclName().StartsWith("_solve_"))
                            goto done;
                        goals.Add(arg);
                        memo.Add(arg, arg);
                        goto done;
                    }
                    else
                        return CollectGoalsRec(memo, arg, goals, cruft);
                }
                else if (f.GetKind() == DeclKind.Uninterpreted)
                {
                    string name = f.GetDeclName();
                    if (name.StartsWith("_solve_"))
                    {
                        if (memo.TryGetValue(t, out res))
                            goto done;
                        goals.Add(t);
                        memo.Add(t, t);
                        return t;
                    }
                }
            }
            // else the goal must be cruft
            cruft.Add(t);
        done:
            res = t; // just to return something
            memo.Add(t, res);
            return res;
        }

        private void CollectGoals(Term t, List<Term> goals, List<Term> cruft)
        {
            TermDict< Term> memo = new TermDict< Term>();
            CollectGoalsRec(memo, t.GetAppArgs()[1], goals, cruft);
        }

        private Term SubstRec(TermDict< Term> memo, Term t)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            var kind = t.GetKind();
            if (kind == TermKind.App)
            {
                // var f = t.GetAppDecl();
                var args = t.GetAppArgs().Select(x => SubstRec(memo, x)).ToArray();
                res = ctx.CloneApp(t, args);
            }
            else res = t;
            memo.Add(t, res);
            return res;
        }

        private Term SubstRecGoals(TermDict< Term> memo, Term t)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            var kind = t.GetKind();
            if (kind == TermKind.App)
            {
                var f = t.GetAppDecl();
                var args = t.GetAppArgs();
                if (f.GetKind() == DeclKind.Implies){
                    res = SubstRecGoals(memo, args[1]);
                    if (res != ctx.MkTrue())
                      res = ctx.MkImplies(args[0],res);
                    goto done;
                }
                else if (f.GetKind() == DeclKind.And)
                {
                    args = args.Select(x => SubstRecGoals(memo, x)).ToArray();
                    args = args.Where(x => x != ctx.MkTrue()).ToArray();
                    res = ctx.MkAnd(args);
                    goto done;
                }
                else if (f.GetKind() == DeclKind.Label)
                {
                    var arg = t.GetAppArgs()[0];
                    if (arg.GetKind() == TermKind.App && arg.GetAppDecl().GetKind() == DeclKind.Uninterpreted)
                    {
                        var r = arg.GetAppDecl();
                        if (memo.TryGetValue(arg, out res))
                        {
                            if(res != ctx.MkTrue())
                                res = ctx.MkApp(f, res);
                            goto done;
                        }
                    }
                    else
                    {
                        res = ctx.MkApp(f, SubstRecGoals(memo, arg));
                        goto done;
                    }

                }
                // what's left could be cruft!
                if (memo.TryGetValue(t, out res))
                {
                    goto done;
                }
            }
            res = t;
          done:
            memo.Add(t, res);
            return res;
        }
        
        private void FactorVCs(Term t, List<Term> vcs)
        {
            List<Term> small = new List<Term>();
            ExtractSmallerVCs(t, small);
            foreach (var smm in small)
            {
                List<Term> goals = new List<Term>();
                List<Term> cruft = new List<Term>();
                var sm = largeblock ? MergeGoals(smm) : smm;
                CollectGoals(sm, goals,cruft);
                foreach (var goal in goals)
                {
                    TermDict< Term> memo = new TermDict< Term>();
                    foreach (var othergoal in goals)
                        memo.Add(othergoal, othergoal.Equals(goal) ? ctx.MkFalse() : ctx.MkTrue());
                    foreach (var thing in cruft)
                        memo.Add(thing, ctx.MkTrue());
                    var vc = SubstRecGoals(memo, sm);
                    vc = ctx.MkImplies(ctx.MkNot(vc), goal);
                    vcs.Add(vc);
                }
                {
                    TermDict< Term> memo = new TermDict< Term>();
                    foreach (var othergoal in goals)
                        memo.Add(othergoal, ctx.MkTrue());
                    var vc = SubstRecGoals(memo, sm);
                    if (vc != ctx.MkTrue())
                    {
                        vc = ctx.MkImplies(ctx.MkNot(vc), ctx.MkFalse());
                        vcs.Add(vc);
                    }
                }
            }
        }

        

        private void GenerateVCForStratifiedInlining(Program program, StratifiedInliningInfo info, Checker checker)
        {
            Contract.Requires(program != null);
            Contract.Requires(info != null);
            Contract.Requires(checker != null);
            Contract.Requires(info.impl != null);
            Contract.Requires(info.impl.Proc != null);


            
            Implementation impl = info.impl;
            if (mode == Mode.Boogie && style == AnnotationStyle.Flat && impl.Name != main_proc_name)
                return;
            Contract.Assert(impl != null);
            ConvertCFG2DAG(impl,edgesCut);
            VC.ModelViewInfo mvInfo;
            PassifyImpl(impl, out mvInfo);
            Dictionary<int, Absy> label2absy = null;
            VCExpressionGenerator gen = checker.VCExprGen;
            Contract.Assert(gen != null);
            VCExpr vcexpr;
            if(NoLabels){
                // int assertionCount = 0;
                VCExpr startCorrect = null; /* VC.VCGen.LetVC(cce.NonNull(impl.Blocks[0]), null, null, info.blockVariables, info.bindings,
                    info.ctxt, out assertionCount); */
                vcexpr = gen.Let(info.bindings, startCorrect);
            }
            else vcexpr = GenerateVC(impl, null /* info.controlFlowVariable */, out label2absy, info.ctxt);
            if(mode != Mode.Boogie)
                vcexpr = gen.Not(vcexpr);
            Contract.Assert(vcexpr != null);
            info.label2absy = label2absy;
            info.mvInfo = mvInfo;
            List<VCExpr> interfaceExprs = new List<VCExpr>();

            if (true /* was:  !info.isMain */)
            {
                Boogie2VCExprTranslator translator = checker.TheoremProver.Context.BoogieExprTranslator;
                Contract.Assert(translator != null);
                info.privateVars = new List<VCExprVar>();
                foreach (Variable v in impl.LocVars)
                {
                    Contract.Assert(v != null);
                    info.privateVars.Add(translator.LookupVariable(v));
                }
                foreach (Variable v in impl.OutParams)
                {
                    Contract.Assert(v != null);
                    info.privateVars.Add(translator.LookupVariable(v));
                }

                info.interfaceExprVars = new List<VCExprVar>();

                foreach (Variable v in info.interfaceVars)
                {
                    Contract.Assert(v != null);
                    VCExprVar ev = translator.LookupVariable(v);
                    Contract.Assert(ev != null);
                    info.interfaceExprVars.Add(ev);
                    interfaceExprs.Add(ev);
                }
            }

            Function function = cce.NonNull(info.function);
            Contract.Assert(function != null);
            info.funcExpr = gen.Function(function, interfaceExprs);
            info.vcexpr = vcexpr;

            if (mode == Mode.Boogie)
            {
                Term z3vc = boogieContext.VCExprToTerm(vcexpr, linOptions);
                FactorVCs(z3vc, DualityVCs);
            }
            else
            {
                // Index the procedures by relational variable
                FuncDecl R = boogieContext.VCExprToTerm(info.funcExpr, linOptions).GetAppDecl();
                relationToProc.Add(R, info);
                info.node = rpfp.CreateNode(boogieContext.VCExprToTerm(info.funcExpr, linOptions));
                rpfp.nodes.Add(info.node);
                if (info.isMain || QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint"))
                    info.node.Bound.Formula = ctx.MkFalse();
            }
        }

        // This returns a new FuncDel with same sort as top-level function
        // of term t, but with numeric suffix appended to name.

        private FuncDecl SuffixFuncDecl(Term t, int n)
        {
            var name = t.GetAppDecl().GetDeclName() + "_" + n.ToString();
            return ctx.MkFuncDecl(name, t.GetAppDecl());
        }

        // Collect the relational paremeters

        private Term CollectParamsRec(TermDict<Term> memo, Term t, List<FuncDecl> parms, List<RPFP.Node> nodes, Dictionary<Term,Term> done)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            var kind = t.GetKind();
            if (kind == TermKind.App)
            {
                var f = t.GetAppDecl();
                var args = t.GetAppArgs();
                args = args.Select(x => CollectParamsRec(memo, x, parms, nodes, done)).ToArray();
                StratifiedInliningInfo info;
                if (relationToProc.TryGetValue(f, out info))
                {
                    if (done.ContainsKey(t))
                        res = done[t];
                    else
                    {
                        f = SuffixFuncDecl(t, parms.Count);
                        parms.Add(f);
                        nodes.Add(info.node);
                        res = ctx.MkApp(f, args);
                        done.Add(t,res); // don't count same expression twice!
                    }
                }
                else
                    res = ctx.CloneApp(t, args);
            } // TODO: handle quantifiers
            else res = t;
            memo.Add(t, res);
            return res;
        }

        public void GetTransformer(StratifiedInliningInfo info)
        {
            Term vcTerm = boogieContext.VCExprToTerm(info.vcexpr, linOptions);
            Term[] paramTerms = info.interfaceExprVars.Select(x => boogieContext.VCExprToTerm(x, linOptions)).ToArray();
            var relParams = new List<FuncDecl>();
            var nodeParams = new List<RPFP.Node>();
            var memo = new TermDict< Term>();
            var done = new Dictionary<Term,Term>(); // note this hashes on equality, not reference!
            vcTerm = CollectParamsRec(memo, vcTerm, relParams, nodeParams,done);
            // var ops = new Util.ContextOps(ctx);
            // var foo = ops.simplify_lhs(vcTerm);
            // vcTerm = foo.Item1;
            info.F = rpfp.CreateTransformer(relParams.ToArray(), paramTerms, vcTerm);
            info.edge = rpfp.CreateEdge(info.node, info.F, nodeParams.ToArray());
            rpfp.edges.Add(info.edge);
            // TODO labels[info.edge.number] = foo.Item2;
        }

        public RPFP.Node GetNodeOfImpl(Implementation/*!*/ impl)
        {
            return implName2StratifiedInliningInfo[impl.Name].node;
        }

        public class CyclicLiveVariableAnalysis : Microsoft.Boogie.LiveVariableAnalysis
        {
            public new static void ComputeLiveVariables(Implementation impl)
            {

                bool some_change = true;
                List<Block> sortedNodes = new List<Block>();
                foreach (var block in impl.Blocks)
                {
                    sortedNodes.Add(block);
                }
                sortedNodes.Reverse();
             
                while (some_change)
                {
                    some_change = false;
                    foreach (Block/*!*/ block in sortedNodes)
                    {
                        Contract.Assert(block != null);
                        HashSet<Variable/*!*/>/*!*/ liveVarsAfter = new HashSet<Variable/*!*/>();
                        if (block.TransferCmd is GotoCmd)
                        {
                            GotoCmd gotoCmd = (GotoCmd)block.TransferCmd;
                            if (gotoCmd.labelTargets != null)
                            {
                                foreach (Block/*!*/ succ in gotoCmd.labelTargets)
                                {
                                    Contract.Assert(succ != null);
                                    if (succ.liveVarsBefore != null)
                                        liveVarsAfter.UnionWith(succ.liveVarsBefore);
                                }
                            }
                        }

                        List<Cmd> cmds = block.Cmds;
                        int len = cmds.Count;
                        for (int i = len - 1; i >= 0; i--)
                        {
                            if (cmds[i] is CallCmd)
                            {
                                Procedure/*!*/ proc = cce.NonNull(cce.NonNull((CallCmd/*!*/)cmds[i]).Proc);
                                if (InterProcGenKill.HasSummary(proc.Name))
                                {
                                    liveVarsAfter =
                                      InterProcGenKill.PropagateLiveVarsAcrossCall(cce.NonNull((CallCmd/*!*/)cmds[i]), liveVarsAfter);
                                    continue;
                                }
                            }
                            Propagate(cmds[i], liveVarsAfter);
                        }

                        if (block.liveVarsBefore == null)
                            block.liveVarsBefore = new HashSet<Variable>();
                        if (!liveVarsAfter.IsSubsetOf(block.liveVarsBefore))
                        {
                            block.liveVarsBefore = liveVarsAfter;
                            some_change = true;
                        }
                    }
                }
            }
        }

        public void Generate()
        {

            var oldDagOption = CommandLineOptions.Clo.vcVariety;
            CommandLineOptions.Clo.vcVariety = CommandLineOptions.VCVariety.Dag;

            // MarkAllFunctionImplementationsInline(); // This is for SMACK, which goes crazy with functions

            // Run live variable analysis (TODO: should this be here?)
#if false
            if (CommandLineOptions.Clo.LiveVariableAnalysis == 2)
            {
                Microsoft.Boogie.InterProcGenKill.ComputeLiveVars(impl, program);
            }
#endif

            #region In Boogie mode, annotate the program
            if (mode == Mode.Boogie)
            {

                // find the name of the main procedure
                main_proc_name = null; // default in case no entry point defined
                foreach (var impl in program.Implementations)
                {
                    if (QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint"))
                        main_proc_name = impl.Proc.Name;
                }
                if (main_proc_name == null)
                {
                    foreach (var impl in program.Implementations)
                    {
                        if (impl.Proc.Name == "main" || impl.Proc.Name.EndsWith(".main"))
                            main_proc_name = impl.Proc.Name;
                    }
                }
                if (main_proc_name == null)
                    main_proc_name = "main";

                if (style == AnnotationStyle.Flat)
                {
                    InlineAll();
                    Microsoft.Boogie.BlockCoalescer.CoalesceBlocks(program);
                    foreach (var impl in program.Implementations)
                    {
                        if (main_proc_name == impl.Proc.Name)
                        {
                            Microsoft.Boogie.LiveVariableAnalysis.ClearLiveVariables(impl);
                            CyclicLiveVariableAnalysis.ComputeLiveVariables(impl);
                            AnnotateLoops(impl, boogieContext);
                        }
                    }
                }
                else
                {

                    if (style == AnnotationStyle.Procedure || style == AnnotationStyle.Call)
                    {
                        foreach (var impl in program.Implementations)
                        {
                            if (!QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint"))
                                AnnotateProcRequires(impl.Proc, impl, boogieContext);
                            AnnotateProcEnsures(impl.Proc, impl, boogieContext);
                        }
                        if (style == AnnotationStyle.Call)
                        {

                        }
                    }

                    // must do this after annotating procedures, else calls
                    // will be prematurely desugared
                    
                    foreach (var impl in program.Implementations)
                    {
                        Microsoft.Boogie.LiveVariableAnalysis.ClearLiveVariables(impl);
                        CyclicLiveVariableAnalysis.ComputeLiveVariables(impl);
                    }


                    if (style == AnnotationStyle.Flat || style == AnnotationStyle.Call)
                    {
                        foreach (var impl in program.Implementations)
                        {
                            AnnotateLoops(impl, boogieContext);
                        }
                    }
                    if (style == AnnotationStyle.Call)
                    {
                        Dictionary<string, bool> impls = new Dictionary<string, bool>();
                        foreach (var impl in program.Implementations)
                        {
                            impls.Add(impl.Proc.Name, true);
                        }
                        foreach (var impl in program.Implementations)
                        {
                            AnnotateCallSites(impl, boogieContext, impls);
                        }
                    }
                    if (style == AnnotationStyle.Flat)
                        InlineAll();
                }
            }
            #endregion

            /* Generate the VC's */
            GenerateVCsForStratifiedInlining();
 
            /* Generate the background axioms */
            Term background = ctx.MkTrue(); // TODO boogieContext.VCExprToTerm(boogieContext.Axioms, linOptions);
            rpfp.AssertAxiom(background);

            int save_option = CommandLineOptions.Clo.StratifiedInlining; // need this to get funcall labels
            CommandLineOptions.Clo.StratifiedInlining = 1;

            /* Create the nodes, indexing procedures by their relational symbols. */
            foreach (StratifiedInliningInfo info in implName2StratifiedInliningInfo.Values)
                GenerateVCForStratifiedInlining(program, info, checker);

            CommandLineOptions.Clo.StratifiedInlining = save_option;

            if (mode == Mode.Boogie)
            {
                // var ops = new Util.ContextOps(ctx);
                var vcs = DualityVCs;
                DualityVCs = new List<Term>();
                foreach (var vc in vcs)
                {
                    // var foo = ops.simplify_lhs(vc.GetAppArgs()[0]);
                    var foo = vc.GetAppArgs()[0];
                    if (!foo.IsFalse())
                        DualityVCs.Add(ctx.MkImplies(foo, vc.GetAppArgs()[1]));
                }

                rpfp.FromClauses(DualityVCs.ToArray());
                // TODO rpfp.HornClauses = style == AnnotationStyle.Flat;
            }
            else
            {
                /* Generate the edges. */
                foreach (StratifiedInliningInfo info in implName2StratifiedInliningInfo.Values)
                    GetTransformer(info);
            }

            // save some information for debugging purposes
            // TODO rpfp.ls.SetAnnotationInfo(annotationInfo);

            CommandLineOptions.Clo.vcVariety = oldDagOption;
        }

        
        private class ErrorHandler : ProverInterface.ErrorHandler
        {
            //TODO: anything we need to handle?
        }

        Dictionary<int, Dictionary<string, string>> varSubst = null;

        /** Check the RPFP, and return a counterexample if there is one. */

        public VC.ConditionGeneration.Outcome Check(ref RPFP.Node cexroot)
        {
            var start = DateTime.Now;

            ErrorHandler handler = new ErrorHandler();
            RPFP.Node cex;
            varSubst = new Dictionary<int,Dictionary<string,string>>();

#if false
            int origRecursionBound = CommandLineOptions.Clo.RecursionBound;
            if (CommandLineOptions.Clo.RecursionBound > 0 && extraRecBound != null)
            {
                int maxExtra = 0;
                foreach (string s in extraRecBound.Keys)
                {
                    int extra = extraRecBound[s];
                    if (extra > maxExtra) maxExtra = extra;
                }
                CommandLineOptions.Clo.RecursionBound += maxExtra;
            }
#endif
            
            ProverInterface.Outcome outcome =
                 checker.TheoremProver.CheckRPFP("name", rpfp, handler, out cex, varSubst, extraRecBound);
            cexroot = cex;

#if false
            CommandLineOptions.Clo.RecursionBound = origRecursionBound;
#endif
          
            Console.WriteLine("solve: {0}s", (DateTime.Now - start).TotalSeconds);
            
            switch(outcome)
            {
                case ProverInterface.Outcome.Valid:
                    return VC.ConditionGeneration.Outcome.Correct;
                case ProverInterface.Outcome.Bounded:
                    return VC.ConditionGeneration.Outcome.ReachedBound;
                case ProverInterface.Outcome.Invalid:
                    return VC.ConditionGeneration.Outcome.Errors;
                case ProverInterface.Outcome.TimeOut:
                    return VC.ConditionGeneration.Outcome.TimedOut;
                case ProverInterface.Outcome.OutOfResource:
                    return VC.ConditionGeneration.Outcome.OutOfResource;
                default:
                   return VC.ConditionGeneration.Outcome.Inconclusive;
            }
        }

        private bool generated = false;

        static private Object thisLock = new Object();

        public override VC.VCGen.Outcome VerifyImplementation(Implementation impl, VerifierCallback collector)
        {

            lock (thisLock)
            {
                Procedure proc = impl.Proc;

                // we verify all the impls at once, so we need to execute only once
                // TODO: make sure needToCheck is true only once
                bool needToCheck = false;
                if (mode == Mode.OldCorral)
                    needToCheck = proc.FindExprAttribute("inline") == null && !(proc is LoopProcedure);
                else if (mode == Mode.Corral || mode == Mode.Boogie)
                    needToCheck = QKeyValue.FindBoolAttribute(impl.Attributes, "entrypoint") && !(proc is LoopProcedure);
                else
                    needToCheck = impl.Name == main_proc_name;

                if (needToCheck)
                {

                    var start = DateTime.Now;

                    if (!generated)
                    {
                        Generate();
                        Console.WriteLine("generate: {0}s", (DateTime.Now - start).TotalSeconds);
                        generated = true;
                    }


                    Console.WriteLine("Verifying {0}...", impl.Name);

                    RPFP.Node cexroot = null;
                    // start = DateTime.Now;
                    var checkres = Check(ref cexroot);
                    Console.WriteLine("check: {0}s", (DateTime.Now - start).TotalSeconds);
                    switch (checkres)
                    {
                        case Outcome.Errors:
                            Console.WriteLine("Counterexample found.\n");
                            // start = DateTime.Now;
                            Counterexample cex = CreateBoogieCounterExample(cexroot.owner, cexroot, impl);
                            // cexroot.owner.DisposeDualModel();
                            // cex.Print(0);  // just for testing
                            collector.OnCounterexample(cex, "assertion failure");
                            Console.WriteLine("cex: {0}s", (DateTime.Now - start).TotalSeconds);
                            ConjecturesToSpecs();
                            break;
                        case Outcome.Correct:
                            Console.WriteLine("Procedure is correct. (fixed point reached)");
							FixedPointToSpecs();
                            ConjecturesToSpecs();
                            break;
                        case Outcome.ReachedBound:
                            Console.WriteLine("Procedure is correct. (recursion bound reached)");
                            FixedPointToSpecs();
                            ConjecturesToSpecs();
                            break;
                        default:
                            Console.WriteLine("Inconclusive result.");
                            ConjecturesToSpecs();
                            break;
                    }
                    return checkres;
                    
                }

                return Outcome.Inconclusive;
            }
        }

        public void FindLabelsRec(HashSet<Term> memo, Term t, Dictionary<string, Term> res)
        {
            if (memo.Contains(t))
                return;
            if (t.IsLabel())
            {
                string l = t.LabelName();
                if (!res.ContainsKey(l))
                    res.Add(l, t.GetAppArgs()[0]);
            }
            if (t.GetKind() == TermKind.App)
            {
                var args = t.GetAppArgs();
                foreach (var a in args)
                    FindLabelsRec(memo, a, res);
            } // TODO: handle quantifiers
            
            memo.Add(t);
        }

        public void FindLabels()
        {
            labels = new Dictionary<string, Term>();
            foreach(var e in rpfp.edges){
                int id = e.number;
                HashSet<Term> memo = new HashSet<Term>(ReferenceComparer<Term>.Instance);
                FindLabelsRec(memo, e.F.Formula, labels);
            }
        }

        public string CodeLabel(Absy code, StratifiedInliningInfo info, string prefix)
        {
            if (info.label2absyInv == null)
            {
                info.label2absyInv = new Dictionary<Absy, string>();
                foreach (int foo in info.label2absy.Keys)
                {
                    Absy bar = info.label2absy[foo] as Absy;
                    string lbl = foo.ToString();
                    info.label2absyInv.Add(bar, lbl);
                }
            }
            if (info.label2absyInv.ContainsKey(code))
            {
                string label = info.label2absyInv[code];
                return prefix+label;
            }
            return null;
        }

        public Term CodeLabeledExpr(RPFP rpfp, RPFP.Node root, Absy code, StratifiedInliningInfo info, string prefix)
        {
            string label = CodeLabel(code, info, prefix);
            
            if (label != null)
            {
                var res = labels[label];
                return res;
            }
            else return null;
        }

        public class LabelNotFound : Exception { };
        
        public bool CodeLabelTrue(RPFP rpfp, RPFP.Node root, Absy code, StratifiedInliningInfo info, string prefix)
        {
            string label = CodeLabel(code, info, prefix);
            
            if (label == null)
                throw new LabelNotFound();
            return root.Outgoing.labels.Contains(label);
        }

        public bool CodeLabelFalse(RPFP rpfp, RPFP.Node root, Absy code, StratifiedInliningInfo info, string prefix)
        {
            return CodeLabelTrue(rpfp, root, code, info, prefix);
        }


        private class StateId
        {
            public RPFP.Edge edge;
            public int capturePoint;
            public StratifiedInliningInfo info;
            public StateId(RPFP.Edge e, int c, StratifiedInliningInfo i)
            {
                edge = e;
                capturePoint = c;
                info = i;
            }
        }


        public Counterexample CreateBoogieCounterExample(RPFP rpfp, RPFP.Node root, Implementation mainImpl)
        {
            FindLabels();
            var orderedStateIds = new List<StateId>();
            Counterexample newCounterexample =
              GenerateTrace(rpfp, root, orderedStateIds, mainImpl,true);
            if (CommandLineOptions.Clo.ModelViewFile != null)
            {
                Model m = root.owner.GetBackgroundModel();
                GetModelWithStates(m, root, implName2StratifiedInliningInfo[mainImpl.Name],
                                   orderedStateIds, varSubst);
                newCounterexample.Model = m;
            }
            return newCounterexample;
        }

        

        private Counterexample GenerateTrace(RPFP rpfp, RPFP.Node root,
                                                 List<StateId> orderedStateIds, Implementation procImpl, bool toplevel)
        {
            Contract.Requires(procImpl != null);

            Contract.Assert(!rpfp.Empty(root));


            var info = implName2StratifiedInliningInfo[procImpl.Name]; 
            Block entryBlock = cce.NonNull(procImpl.Blocks[0]);
            Contract.Assert(entryBlock != null);
           
            List<Block> trace = new List<Block>(); 
            trace.Add(entryBlock);

            var calleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();

            Counterexample newCounterexample =
                GenerateTraceRec(rpfp, root, orderedStateIds, entryBlock, trace, calleeCounterexamples, info, toplevel);

            return newCounterexample;
        }

        // TODO: this is a bit cheesy. Rather than finding the argument position
        // of a relational term in a transformer by linear search, better to index this
        // somewhere, but where?
        private int TransformerArgPosition(RPFP rpfp, RPFP.Node root, Term expr)
        {
            FuncDecl rel = expr.GetAppDecl();
            string relname = rel.GetDeclName();
            var rps = root.Outgoing.F.RelParams;
            for (int i = 0; i < rps.Length; i++)
            {
                string thisname = rps[i].GetDeclName();
                if (thisname == relname)
                    return i;
            }
            return -1;
        }

        private bool EvalToFalse(RPFP rpfp, RPFP.Node root, Term expr,StratifiedInliningInfo info){
            Term res = rpfp.Eval(root.Outgoing,expr);
            return res.Equals(ctx.MkTrue());
        }
        
        private Counterexample GenerateTraceRec(
                              RPFP rpfp, RPFP.Node root,
                              List<StateId> orderedStateIds,
                              Block/*!*/ b, List<Block>/*!*/ trace,
                              Dictionary<TraceLocation/*!*/, CalleeCounterexampleInfo/*!*/>/*!*/ calleeCounterexamples,
                              StratifiedInliningInfo info,
                              bool toplevel)
        {
            Contract.Requires(b != null);
            Contract.Requires(trace != null);
            Contract.Requires(cce.NonNullDictionaryAndValues(calleeCounterexamples));

            Stack<RPFP.Node> continuation_stack = new Stack<RPFP.Node>();

            // If our block is not present, try diving into precondition
            // and push a continuation.
            // TODO: is the precondition always the first child?
            while (!CodeLabelFalse(rpfp, root, b, info, "+"))
            {
                if (root.Outgoing != null && root.Outgoing.Children.Length > 0)
                {
                    continuation_stack.Push(root);
                    root = root.Outgoing.Children[0];
                }
                else
                {
                    // can't find our block
                    Contract.Assert(false);
                    return null;
                }
            }

            // After translation, all potential errors come from asserts.
            while (true)
            {


                List<Cmd> cmds = b.Cmds;
                TransferCmd transferCmd = cce.NonNull(b.TransferCmd);
                for (int i = 0; i < cmds.Count; i++)
                {
                    Cmd cmd = cce.NonNull(cmds[i]);

                    // Skip if 'cmd' not contained in the trace or not an assert
                    if (cmd is AssertCmd)
                    {
                        bool is_failed_assertion = false;
                        if (NoLabels)
                            is_failed_assertion = true; // we assume only assertions on 
                        else
                            is_failed_assertion = CodeLabelTrue(rpfp, root, cmd, info, "@");

                        if (is_failed_assertion)
                        {
                            if (continuation_stack.Count == 0)
                            {
                                Counterexample newCounterexample =
                                    AssertCmdToCounterexample((AssertCmd)cmd, transferCmd, trace, new Microsoft.Boogie.Model(), info.mvInfo,
                                    boogieContext);
                                newCounterexample.AddCalleeCounterexample(calleeCounterexamples);
                                return newCounterexample;
                            }
                            root = continuation_stack.Pop();
                        }
                        continue;
                    }

                    // Counterexample generation for inlined procedures
                    AssumeCmd assumeCmd = cmd as AssumeCmd;
                    if (assumeCmd == null)
                        continue;
                    NAryExpr naryExpr = assumeCmd.Expr as NAryExpr;
                    if (naryExpr == null)
                        continue;
                    string calleeName = naryExpr.Fun.FunctionName;
                    Contract.Assert(calleeName != null);

                    // what is this crap???
                    BinaryOperator binOp = naryExpr.Fun as BinaryOperator;
                    if (binOp != null && binOp.Op == BinaryOperator.Opcode.And)
                    {
                        Expr expr = naryExpr.Args[0];
                        NAryExpr mvStateExpr = expr as NAryExpr;
                        if (mvStateExpr != null && mvStateExpr.Fun.FunctionName == VC.ModelViewInfo.MVState_FunctionDef.Name)
                        {
                            LiteralExpr x = mvStateExpr.Args[1] as LiteralExpr;
                            // Debug.Assert(x != null);
                            int foo = x.asBigNum.ToInt;
                            orderedStateIds.Add(new StateId(root.Outgoing,foo,info));
                        }
                    }

                    if (calleeName.EndsWith("_summary"))
                        calleeName = calleeName.Substring(0, calleeName.Length - 8);

                    if (!implName2StratifiedInliningInfo.ContainsKey(calleeName) && !calleeName.EndsWith("_summary"))
                        continue;

                    {
                        Term code = CodeLabeledExpr(rpfp, root, cmd, info, "+si_fcall_");
                        int pos = TransformerArgPosition(rpfp, root, code);
                        if (pos >= 0)
                        {
                            RPFP.Node callee = root.Outgoing.Children[pos];
                            orderedStateIds.Add(new StateId(callee.Outgoing, CALL,info));
                            calleeCounterexamples[new TraceLocation(trace.Count - 1, i)] =
                                new CalleeCounterexampleInfo(
                                    cce.NonNull(GenerateTrace(rpfp, callee, orderedStateIds,
                                                implName2StratifiedInliningInfo[calleeName].impl, false)),
                                    new List<object>());
                            orderedStateIds.Add(new StateId(root.Outgoing, RETURN,info));
                        }
                    }
                }

                GotoCmd gotoCmd = transferCmd as GotoCmd;
                List<Block> cuts = null;
                if (edgesCut.ContainsKey(b))
                    cuts = edgesCut[b];
                b = null; 
                
                if (gotoCmd != null)
                {    

                    foreach (Block bb in cce.NonNull(gotoCmd.labelTargets))
                    {
                        Contract.Assert(bb != null);
                        if (CodeLabelFalse(rpfp, root, bb, info, "+"))
                        {
                            trace.Add(bb);
                            b = bb;
                            break;
                        }
                    }
                    if (b != null) continue;
                }
                // HACK: we have to try edges that were cut in generating the VC

                if (cuts != null)
                    foreach (var bb in cuts)
                    {
                        if (CodeLabelFalse(rpfp, root, bb, info, "+"))
                        {
                            trace.Add(bb);
                            b = bb;
                            break;
                        }
                    }
                if (b != null) continue;

                return null;
            }

            
        }

        public override Counterexample extractLoopTrace(Counterexample cex, string mainProcName, Program program, Dictionary<string, Dictionary<string, Block>> extractLoopMappingInfo)
        {
            // Construct the set of inlined procs in the original program
            var inlinedProcs = new HashSet<string>();
            foreach (var decl in program.TopLevelDeclarations)
            {
                // Implementations
                if (decl is Implementation)
                {
                    var impl = decl as Implementation;
                    if (!(impl.Proc is LoopProcedure))
                    {
                        inlinedProcs.Add(impl.Name);
                    }
                }

                // And recording procedures
                if (decl is Procedure)
                {
                    var proc = decl as Procedure;
                    if (proc.Name.StartsWith(recordProcName))
                    {
                        // Debug.Assert(!(decl is LoopProcedure));
                        inlinedProcs.Add(proc.Name);
                    }
                }
            }
            return extractLoopTraceRec(
              new CalleeCounterexampleInfo(cex, new List<object>()),
              mainProcName, inlinedProcs, extractLoopMappingInfo).counterexample;
        }

        protected override bool elIsLoop(string procname)
        {
            StratifiedInliningInfo info = null;
            if (implName2StratifiedInliningInfo.ContainsKey(procname))
            {
                info = implName2StratifiedInliningInfo[procname];
            }

            if (info == null) return false;

            var lp = info.impl.Proc as LoopProcedure;

            if (lp == null) return false;
            return true;
        }

        private void NumberCexEdges(RPFP.Node node, Dictionary<int,RPFP.Edge> map)
        {
            if (node.Outgoing == null)
                return; // shouldn't happen
            RPFP.Edge edge = node.Outgoing;
            map[edge.number] = edge;
            foreach (var c in edge.Children)
                NumberCexEdges(c, map);
        }

        private void GetModelWithStates(Model m, RPFP.Node cex, StratifiedInliningInfo mainInfo,
                                        List<StateId> orderedStateIds,
                                        Dictionary<int,Dictionary<string,string>> varSubst)
        {
            if (m == null) return;
            var mvInfo = mainInfo.mvInfo;
            

            foreach (Variable v in mvInfo.AllVariables)
            {
                m.InitialState.AddBinding(v.Name, GetModelValue(m, v, varSubst[cex.Outgoing.number]));
            }

            Dictionary<int, RPFP.Edge> edgeNumbering = new Dictionary<int,RPFP.Edge>();
            NumberCexEdges(cex, edgeNumbering);

            int lastCandidate = 0;
            int lastCapturePoint = CALL;
            for (int i = 0; i < orderedStateIds.Count; ++i)
            {
                var s = orderedStateIds[i];
                RPFP.Edge edge = s.edge;
                int candidate = edge.number;
                int capturePoint = s.capturePoint;
                Dictionary<string, string> subst = varSubst[candidate];

                string implName = edge.Parent.Name.GetDeclName();
                var info = s.info.mvInfo;

                if (capturePoint == CALL || capturePoint == RETURN)
                {
                    lastCandidate = candidate;
                    lastCapturePoint = capturePoint;
                    continue;
                }

                Contract.Assume(0 <= capturePoint && capturePoint < info.CapturePoints.Count);
                VC.ModelViewInfo.Mapping map = info.CapturePoints[capturePoint];
                var prevInc = (lastCapturePoint != CALL && lastCapturePoint != RETURN && candidate == lastCandidate)
                  ? info.CapturePoints[lastCapturePoint].IncarnationMap : new Dictionary<Variable, Expr>();
                var cs = m.MkState(map.Description);

                foreach (Variable v in info.AllVariables)
                {
                    var e = (Expr)map.IncarnationMap[v];

                    if (e == null)
                    {
                        if (lastCapturePoint == CALL || lastCapturePoint == RETURN)
                        {
                            cs.AddBinding(v.Name, GetModelValue(m, v, subst));
                        }
                        continue;
                    }

                    if (lastCapturePoint != CALL && lastCapturePoint != RETURN && prevInc[v] == e) continue; // skip unchanged variables

                    Model.Element elt;
                    if (e is IdentifierExpr)
                    {
                        IdentifierExpr ide = (IdentifierExpr)e;
                        elt = GetModelValue(m, ide.Decl, subst);
                    }
                    else if (e is LiteralExpr)
                    {
                        LiteralExpr lit = (LiteralExpr)e;
                        elt = m.MkElement(lit.Val.ToString());
                    }
                    else
                    {
                        Contract.Assume(false);
                        elt = m.MkFunc(e.ToString(), 0).GetConstant();
                    }
                    cs.AddBinding(v.Name, elt);
                }

                lastCandidate = candidate;
                lastCapturePoint = capturePoint;
            }

            return;
        }


        public readonly static int CALL = -1;
        public readonly static int RETURN = -2;

        private Model.Element GetModelValue(Model m, Variable v, Dictionary<string,string> subst)
        {
            // first, get the unique name
            string uniqueName;

            VCExprVar vvar = boogieContext.BoogieExprTranslator.TryLookupVariable(v);
            
            uniqueName = v.Name;
            
            if(subst.ContainsKey(uniqueName))
                return m.MkElement(subst[uniqueName]);
            return m.MkFunc("@undefined", 0).GetConstant();
        }
		
		class InternalError : Exception {
		}
		
		
		private BinaryOperator.Opcode VCOpToOp (VCExprOp op)
		{
			if (op == VCExpressionGenerator.AddIOp)
				return BinaryOperator.Opcode.Add;
			if (op == VCExpressionGenerator.SubIOp)
				return BinaryOperator.Opcode.Sub;
			if (op == VCExpressionGenerator.MulIOp)
				return BinaryOperator.Opcode.Mul;
			if (op == VCExpressionGenerator.DivIOp)
				return BinaryOperator.Opcode.Div;
			if (op == VCExpressionGenerator.EqOp)
				return BinaryOperator.Opcode.Eq;
			if (op == VCExpressionGenerator.LeOp)
				return BinaryOperator.Opcode.Le;
			if (op == VCExpressionGenerator.LtOp)
				return BinaryOperator.Opcode.Lt;
			if (op == VCExpressionGenerator.GeOp)
				return BinaryOperator.Opcode.Ge;
			if (op == VCExpressionGenerator.GtOp)
				return BinaryOperator.Opcode.Gt;
			if (op == VCExpressionGenerator.AndOp)
				return BinaryOperator.Opcode.And;
			if (op == VCExpressionGenerator.OrOp)
				return BinaryOperator.Opcode.Or;
			throw new InternalError();
		}
		
		private Expr MakeBinary (BinaryOperator.Opcode op, List<Expr> args)
		{
			if(args.Count == 0){
				// with zero args we need the identity of the op
				switch(op){
					case BinaryOperator.Opcode.And:
					    return Expr.True;
					case BinaryOperator.Opcode.Or:
					    return Expr.False;
				    case BinaryOperator.Opcode.Add:
						return new LiteralExpr(Token.NoToken,Microsoft.Basetypes.BigNum.ZERO);
				default:
					throw new InternalError();
				}
			}
			var temp = args[0];
			for(int i = 1; i < args.Count; i++)
				temp = Expr.Binary(Token.NoToken,op,temp,args[i]);
			return temp;		
		}
		
		private Variable MakeVar(VCExprVar v){
			var foo = new TypedIdent(Token.NoToken,v.Name.ToString(),v.Type);
			return new BoundVariable(Token.NoToken,foo);
		}
		
		private Expr VCExprToExpr (VCExpr e, Dictionary<VCExpr,Expr> bound)
		{
			if (e is VCExprVar) {
				if(bound.ContainsKey(e))
					return bound[e];
                return Expr.Ident(MakeVar(e as VCExprVar)); // TODO: this isn't right
			}
			if (e is VCExprIntLit) {
				var n = e as VCExprIntLit;
				return new LiteralExpr(Token.NoToken,n.Val);
			}
			if (e is VCExprNAry) {
				var f = e as VCExprNAry;
				var args = new List<Expr>();
				for(int i = 0; i < f.Arity; i++){
					args.Add (VCExprToExpr (f[i],bound));
				}
				
				if(f.Op == VCExpressionGenerator.NotOp)
					return Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, args[0]);

				if(f.Op == VCExpressionGenerator.IfThenElseOp)
					return new NAryExpr(Token.NoToken,new IfThenElse(Token.NoToken),args);
					
				if(f.Op is VCExprSelectOp){
					var idx = new List<Expr>();
					idx.Add(args[1]);
				    return Expr.Select(args[0],idx);
				}
				
				if(f.Op is VCExprStoreOp){
					var idx = new List<Expr>();
					idx.Add(args[1]);
					return Expr.Store(args[0],idx,args[2]);
				}

                if (f.Op is VCExprBoogieFunctionOp)
                {
                    return new NAryExpr(Token.NoToken, 
                        new FunctionCall((f.Op as VCExprBoogieFunctionOp).Func), args);
                }

				var op = VCOpToOp (f.Op);
				return MakeBinary(op,args);
			}
			
			if(e is VCExprQuantifier) {
				var f = e as VCExprQuantifier;
				var vs = new List<Variable>();
				var new_bound = new Dictionary<VCExpr,Expr>(bound);
				foreach(var v in f.BoundVars){
					var ve = MakeVar(v);
					vs.Add(ve);
					new_bound.Add (v,Expr.Ident (ve));
				}
				var bd = VCExprToExpr(f.Body,new_bound);
				if(f.Quan == Quantifier.EX)
					return new ExistsExpr(Token.NoToken,vs,bd);
				else
					return new ForallExpr(Token.NoToken,vs,bd);	
			}
			if (e == VCExpressionGenerator.True) {
				return Expr.True;
			}
			if (e == VCExpressionGenerator.False) {
				return Expr.False;
			}
			if (e is VCExprLet) {
				
			}
			
			throw new InternalError();
		}
		

    }


}
