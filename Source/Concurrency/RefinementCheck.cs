using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie.GraphUtil;
using System.Diagnostics;
using System.Diagnostics.Contracts;


namespace Microsoft.Boogie
{
    using Bpl = Microsoft.Boogie;
    class RefinementCheck
    {
        Program refinementCheckerProgram;
        LinearTypeChecker linearTypeChecker;
        MoverTypeChecker moverTypeChecker;


        public static void AddCheckers(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker)
        {
            RefinementCheck refinementChecking = new RefinementCheck(linearTypeChecker, moverTypeChecker);
            foreach (Declaration decl in linearTypeChecker.program.TopLevelDeclarations)
            {
                if (decl is Implementation)
                {
                    Implementation impl = decl as Implementation;
                    refinementChecking.createRefinementChecker(impl);
                }
            }
        }

        private RefinementCheck(LinearTypeChecker linearTypeChecker, MoverTypeChecker moverTypeChecker)
        {
            this.linearTypeChecker = linearTypeChecker;
            this.moverTypeChecker = moverTypeChecker;
            this.refinementCheckerProgram = new Program();
            foreach (Declaration decl in linearTypeChecker.program.TopLevelDeclarations)
            {
                if (decl is TypeCtorDecl || decl is TypeSynonymDecl || decl is Constant || decl is Function || decl is Axiom)
                    this.refinementCheckerProgram.TopLevelDeclarations.Add(decl);
            }
            foreach (Variable v in linearTypeChecker.program.GlobalVariables())
            {
                this.refinementCheckerProgram.TopLevelDeclarations.Add(v);
            }
        }

        private void createRefinementChecker(Implementation impl)
        {
            addRefinementCheckingAnnotations(impl);
            refinementCheckerProgram.TopLevelDeclarations.Add(impl);
            refinementCheckerProgram.TopLevelDeclarations.Add(impl.Proc);
        }

        private Expr createNewAlpha(Implementation impl)
        {
            Expr result;
            result = Expr.True;
            foreach (AssertCmd aC in moverTypeChecker.procToActionInfo[impl.Proc].thisGate)
            {
                Expr aCExprClone = (Expr)aC.OrigExpr.Clone();
                result = Expr.Binary(BinaryOperator.Opcode.And, result, aCExprClone);
            }
            return result;
        }

        private Expr createNewAlphaOfGOld(Implementation impl, List<Variable> originalGVars,
            Dictionary<Variable, Variable> regularToOldGVar)
        {
            Expr result;
            result = Expr.True;
            foreach (AssertCmd aC in moverTypeChecker.procToActionInfo[impl.Proc].thisGate)
            {
                Expr aCExprClone = (Expr)aC.OrigExpr.Clone();
                result = Expr.Binary(BinaryOperator.Opcode.And, result, aCExprClone);
            }
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            foreach (Variable v in originalGVars)
            {
                map[v] = Expr.Ident(regularToOldGVar[v]);
            }
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            MySubstituter mySubst = new MySubstituter(subst, subst);// ST: Check with Shaz
            result = (Expr)mySubst.Visit(result);
            return result;
        }


        private HavocCmd createNewHavocGCmd()
        {
            List<IdentifierExpr> gList = new List<IdentifierExpr>();
            foreach (GlobalVariable g in refinementCheckerProgram.GlobalVariables())
                gList.Add(new IdentifierExpr(Token.NoToken, g));
            HavocCmd havocG = new HavocCmd(Token.NoToken, gList);
            return havocG;
        }

        private AssignCmd createNewAssignGOldGetsG(List<Variable> originalGVars, Dictionary<Variable, Variable> regularToOldGVar)
        {
            List<AssignLhs> lhss_g = new List<AssignLhs>();
            List<Expr> rhss_g = new List<Expr>();
            foreach (Variable g in originalGVars)
            {
                rhss_g.Add(new IdentifierExpr(Token.NoToken, g));
                lhss_g.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(regularToOldGVar[g])));
            }

            AssignCmd gOldGetsG = new AssignCmd(Token.NoToken, lhss_g, rhss_g);
            return gOldGetsG;
        }

        private AssignCmd createNewAssignOOldGetsO(Implementation impl, Dictionary<Variable, Variable> regularToOldOVar)
        {
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (Variable o in impl.OutParams)
            {
                rhss.Add(new IdentifierExpr(Token.NoToken, o));
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(regularToOldOVar[o])));
            }

            // Implement command list that does o_old := o;
            AssignCmd oOldGetsO = new AssignCmd(Token.NoToken, lhss, rhss);
            return oOldGetsO;
        }

        private AssertCmd createNewAssertGOldEqualsG(List<Variable> originalGVars, Dictionary<Variable, Variable> regularToOldGVar)
        {
            Expr gOldEqualsG = Expr.True;
            foreach (Variable g in originalGVars)
            {
                Expr thisVarEqualsOldVar = Expr.Binary(BinaryOperator.Opcode.Eq,
                                                       new IdentifierExpr(Token.NoToken, g),
                                                       new IdentifierExpr(Token.NoToken, regularToOldGVar[g]));
                gOldEqualsG = Expr.Binary(BinaryOperator.Opcode.And, gOldEqualsG, thisVarEqualsOldVar);
            }

            AssertCmd AssertGOldEqualsGCmd = new AssertCmd(Token.NoToken, gOldEqualsG);
            return AssertGOldEqualsGCmd;
        }

        private Expr createNewGOldEqualsG(List<Variable> originalGVars, Dictionary<Variable, Variable> regularToOldGVar)
        {
            Expr gOldEqualsG = Expr.True;
            foreach (Variable g in originalGVars)
            {
                Expr thisVarEqualsOldVar = Expr.Binary(BinaryOperator.Opcode.Eq,
                                                       new IdentifierExpr(Token.NoToken, g),
                                                       new IdentifierExpr(Token.NoToken, regularToOldGVar[g]));
                gOldEqualsG = Expr.Binary(BinaryOperator.Opcode.And, gOldEqualsG, thisVarEqualsOldVar);
            }

            return gOldEqualsG;
        }

        private AssertCmd createNewAssertOOldEqualsO(Implementation impl, Dictionary<Variable, Variable> regularToOldOVar)
        {
            Expr oOldEqualsO = Expr.True;
            foreach (Variable o in impl.OutParams)
            {
                Expr thisOVarEqualsOldOVar = Expr.Binary(BinaryOperator.Opcode.Eq,
                                                       new IdentifierExpr(Token.NoToken, o),
                                                       new IdentifierExpr(Token.NoToken, regularToOldOVar[o]));
                oOldEqualsO = Expr.Binary(BinaryOperator.Opcode.And, oOldEqualsO, thisOVarEqualsOldOVar);
            }

            AssertCmd AssertOOldEqualsOCmd = new AssertCmd(Token.NoToken, oOldEqualsO);
            return AssertOOldEqualsOCmd;
        }

        private Expr createNewOOldEqualsO(Implementation impl, Dictionary<Variable, Variable> regularToOldOVar)
        {
            Expr oOldEqualsO = Expr.True;
            foreach (Variable o in impl.OutParams)
            {
                Expr thisOVarEqualsOldOVar = Expr.Binary(BinaryOperator.Opcode.Eq,
                                                       new IdentifierExpr(Token.NoToken, o),
                                                       new IdentifierExpr(Token.NoToken, regularToOldOVar[o]));
                oOldEqualsO = Expr.Binary(BinaryOperator.Opcode.And, oOldEqualsO, thisOVarEqualsOldOVar);
            }

            return oOldEqualsO;
        }


        private Expr createNewBetaOfOldOOldGoNg(Implementation impl, List<Variable> originalGVars,
            Dictionary<Variable, Variable> regularToOldGVar,
            Dictionary<Variable, Variable> regularToOldOVar)
        {
            Expr betaOfOOldOGOldG = new TransitionRelationComputation(moverTypeChecker.program,
                                                          moverTypeChecker.procToActionInfo[impl.Proc],
                                                          regularToOldGVar,
                                                          regularToOldOVar).Compute();
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            foreach (Variable v in originalGVars)
            {
                map[v] = Expr.Ident(regularToOldGVar[v]);
            }
            foreach (Variable o in impl.OutParams)
            {
                map[o] = Expr.Ident(regularToOldOVar[o]);
            }

            Substitution always = Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>());
            Substitution forold = Substituter.SubstitutionFromHashtable(map);
            betaOfOOldOGOldG = Substituter.ApplyReplacingOldExprs(always, forold, betaOfOOldOGOldG);
            return betaOfOOldOGOldG;
        }

        private HavocCmd createNewHavocGnO(Implementation impl, List<Variable> originalGVars)
        {
            HavocCmd resultCmd;
            List<IdentifierExpr> varsList = new List<IdentifierExpr>();
            foreach (Variable gv in originalGVars)
            {
                varsList.Add(new IdentifierExpr(Token.NoToken, gv));
            }
            foreach (Variable v in impl.OutParams)
            {
                varsList.Add(new IdentifierExpr(Token.NoToken, v));
            }
            resultCmd = new HavocCmd(Token.NoToken, varsList);
            return resultCmd;
        }

        private void addRefinementCheckingAnnotations(Implementation impl)
        {
            // Create variables for pc, ok
            LocalVariable pc = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "pc", Bpl.Type.Bool));
            impl.LocVars.Add(pc);
            LocalVariable pc_old = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "pc_old", Bpl.Type.Bool));
            impl.LocVars.Add(pc_old);
            LocalVariable ok = new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "ok", Bpl.Type.Bool));
            impl.LocVars.Add(ok);


            // Create variables for g_old, o_old
            Dictionary<Variable, Variable> regularToOldGVar = new Dictionary<Variable, Variable>();
            Dictionary<Variable, Variable> regularToOldOVar = new Dictionary<Variable, Variable>();
            ActionInfo actionInfoForThisProc = moverTypeChecker.procToActionInfo[impl.Proc];

            List<Variable> originalGVars = new List<Variable>();
            List<Variable> _old_OriginalGVars = new List<Variable>();


            foreach (GlobalVariable gv in refinementCheckerProgram.GlobalVariables())
                originalGVars.Add(gv);

            foreach (Variable v in refinementCheckerProgram.GlobalVariables()) //ST: Check that this is the right set of global vars
            {
                GlobalVariable gv = v as GlobalVariable;
                LocalVariable v_old = new LocalVariable(Token.NoToken,
                    new TypedIdent(Token.NoToken, gv.TypedIdent.Name + "_old", gv.TypedIdent.Type)); //gv.TypedIdent
                impl.LocVars.Add(v_old); //ST: Ask Shaz whether to add v_old to proc, probably not.
                _old_OriginalGVars.Add(v_old);
                regularToOldGVar.Add(gv, v_old);
            }

            // List<Variable> originalOVars = new List<Variable>();
            List<Variable> _old_OriginalOVars = new List<Variable>();


            //foreach (Variable v in impl.OutParams)
            //    originalOVars.Add(v);

            foreach (Variable o in impl.OutParams) //ST: Check that this is the right set of global vars
            {
                Variable o_old = new LocalVariable(Token.NoToken,
                    new TypedIdent(Token.NoToken, o.TypedIdent.Name + "_old", o.TypedIdent.Type));

                _old_OriginalOVars.Add(o_old);
                regularToOldOVar.Add(o, o_old);
            }


            // AssertCmd AssertONGEqualOldONG = new AssertCmd(Token.NoToken, Expr.Binary(BinaryOperator.Opcode.And, oOldEqualsO, gOldEqualsG));

            // Traverse CFG of impl, replace yield's in place.
            foreach (Block b in impl.Blocks)
            {
                List<Cmd> newCmdList = new List<Cmd>();
                foreach (Cmd c in b.Cmds)
                {
                    if (c is YieldCmd)
                    {
                        // Code to be inserted instead of yield
                        // 
                        // assert !pc ==> \alpha(g_old);
                        // assert ok;
                        // if (o_old == o && g_old == g) { // IfCmd
                        //    // Do nothing
                        // } else {
                        //    assert !pc;
                        //    pc := true;
                        //    assert \beta(o_old, g_old, o, g);
                        // }
                        // havoc o, g;
                        // o_old := o;
                        // g_old := g;

                        // Implementing the following instead:

                        // assert !pc ==> \alpha(g_old);
                        // assert ok;
                        // bb := (o_old == o && g_old == g) 
                        // assert !bb ==> !pc;
                        // pc := ite(!bb,true,pc);
                        // assert !bb ==> \beta(o_old, g_old, o, g);
                        // }
                        // havoc o, g;
                        // o_old := o;
                        // g_old := g;

                        Expr notPcImpliesAlphaOfGoldExpr = Expr.Binary(BinaryOperator.Opcode.Imp,
                                                                       Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not,
                                                                                    Expr.Ident(pc)),
                                                                       createNewAlphaOfGOld(impl, originalGVars, regularToOldGVar)
                                                                       );
                        AssertCmd notPcImpliesAlphaOfGOldCmd = new AssertCmd(Token.NoToken, notPcImpliesAlphaOfGoldExpr);
                        newCmdList.Add(notPcImpliesAlphaOfGOldCmd);
                        AssertCmd assertOkCmd = new AssertCmd(Token.NoToken, new IdentifierExpr(Token.NoToken, ok));
                        newCmdList.Add(assertOkCmd);

                        Expr bb = Expr.Binary(BinaryOperator.Opcode.And,
                                    createNewOOldEqualsO(impl, regularToOldOVar),
                                    createNewGOldEqualsG(originalGVars, regularToOldGVar));
                        Expr notBB = Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, bb);
                        Expr notPC = Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, Expr.Ident(pc));
                        AssertCmd assertNotBBImpliesNotPCCmd = new AssertCmd(Token.NoToken, Expr.Imp(notBB, notPC));
                        newCmdList.Add(assertNotBBImpliesNotPCCmd);

                        // pc := ite(!bb,true,pc);
                        List<Expr> iteArgs = new List<Expr>();
                        iteArgs.Add(Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, bb));
                        iteArgs.Add(Expr.True);
                        iteArgs.Add(Expr.Ident(pc));
                        Expr pcNew = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), iteArgs);
                        List<AssignLhs> pcUpdateLHS = new List<AssignLhs>();
                        pcUpdateLHS.Add(new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, pc)));
                        List<Expr> pcUpdateRHS = new List<Expr>();
                        pcUpdateRHS.Add(pcNew);
                        AssignCmd pcGetsUpdated = new AssignCmd(Token.NoToken, pcUpdateLHS, pcUpdateRHS);

                        // assert !bb ==> \beta(o_old, g_old, o, g);
                        Expr betaExpr = createNewBetaOfOldOOldGoNg(impl, originalGVars, regularToOldGVar, regularToOldOVar);
                        AssertCmd betaAssertCmd = new AssertCmd(Token.NoToken, Expr.Imp(Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, bb),
                                                                                        betaExpr));
                        newCmdList.Add(betaAssertCmd);

                        HavocCmd havocOnG = createNewHavocGnO(impl, originalGVars);
                        newCmdList.Add(havocOnG);

                        if (originalGVars.Count > 0)
                        {
                            AssignCmd gOldGetsG = createNewAssignGOldGetsG(originalGVars, regularToOldGVar);
                            newCmdList.Add(gOldGetsG);
                        }

                        if (impl.OutParams.Count > 0)
                        {
                            AssignCmd oOldGetsO = createNewAssignOOldGetsO(impl, regularToOldOVar);
                            newCmdList.Add(oOldGetsO);
                        }
                    }
                    else
                    {
                        newCmdList.Add((Cmd)c.Clone());
                    }
                }
                b.Cmds = newCmdList;
            }
        }
    }
    
    sealed class MySubstituter : Duplicator
    {
        private readonly Substitution outsideOld;
        private readonly Substitution insideOld;
        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(insideOld != null);
        }

        public MySubstituter(Substitution outsideOld, Substitution insideOld)
            : base()
        {
            Contract.Requires(outsideOld != null && insideOld != null);
            this.outsideOld = outsideOld;
            this.insideOld = insideOld;
        }

        private bool insideOldExpr = false;

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            Contract.Ensures(Contract.Result<Expr>() != null);
            Expr e = null;

            if (insideOldExpr)
            {
                e = insideOld(node.Decl);
            }
            else
            {
                e = outsideOld(node.Decl);
            }
            return e == null ? base.VisitIdentifierExpr(node) : e;
        }

        public override Expr VisitOldExpr(OldExpr node)
        {
            Contract.Ensures(Contract.Result<Expr>() != null);
            bool previouslyInOld = insideOldExpr;
            insideOldExpr = true;
            Expr tmp = (Expr)this.Visit(node.Expr);
            OldExpr e = new OldExpr(node.tok, tmp);
            insideOldExpr = previouslyInOld;
            return e;
        }
    }

    class TransitionRelationComputation
    {
        private Program program;
        private ActionInfo first;
        private ActionInfo second;
        private Stack<Block> dfsStack;
        private Expr transitionRelation;
        private Dictionary<Variable, Variable> regularToOldGVar;
        private Dictionary<Variable, Variable> regularToOldOVar;

        public TransitionRelationComputation(Program program, ActionInfo second, Dictionary<Variable, Variable> regularToOldGVar, Dictionary<Variable, Variable> regularToOldOVar)
        {
            this.program = program;
            this.first = null;
            this.second = second;
            this.regularToOldGVar = regularToOldGVar;
            this.regularToOldOVar = regularToOldOVar;
            this.dfsStack = new Stack<Block>();
            this.transitionRelation = Expr.False;
        }

        public Expr Compute()
        {
            Search(second.thatAction.Blocks[0], false);
            Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
            List<Variable> boundVars = new List<Variable>();
            if (first != null)
            {
                foreach (Variable v in first.thisAction.LocVars)
                {
                    BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
                    map[v] = new IdentifierExpr(Token.NoToken, bv);
                    boundVars.Add(bv);
                }
            }
            foreach (Variable v in second.thatAction.LocVars)
            {
                BoundVariable bv = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, v.Name, v.TypedIdent.Type));
                map[v] = new IdentifierExpr(Token.NoToken, bv);
                boundVars.Add(bv);
            }
            Substitution subst = Substituter.SubstitutionFromHashtable(map);
            if (boundVars.Count > 0)
                return new ExistsExpr(Token.NoToken, boundVars, Substituter.Apply(subst, transitionRelation));
            else
                return transitionRelation;
        }

        private Expr CalculatePathCondition()
        {
            Expr returnExpr = Expr.True;
            foreach (Variable v in program.GlobalVariables())
            {
                var eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, v), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                returnExpr = Expr.And(eqExpr, returnExpr);
            }
            if (first != null)
            {
                foreach (Variable v in first.thisOutParams)
                {
                    var eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, v), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                    returnExpr = Expr.And(eqExpr, returnExpr);
                }
            }
            foreach (Variable v in second.thatOutParams)
            {
                var eqExpr = Expr.Eq(new IdentifierExpr(Token.NoToken, v), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, v)));
                returnExpr = Expr.And(eqExpr, returnExpr);
            }
            Block[] dfsStackAsArray = dfsStack.Reverse().ToArray();
            for (int i = dfsStackAsArray.Length - 1; i >= 0; i--)
            {
                Block b = dfsStackAsArray[i];
                for (int j = b.Cmds.Count - 1; j >= 0; j--)
                {
                    Cmd cmd = b.Cmds[j];
                    if (cmd is AssumeCmd)
                    {
                        AssumeCmd assumeCmd = cmd as AssumeCmd;
                        returnExpr = Expr.And(new OldExpr(Token.NoToken, assumeCmd.Expr), returnExpr);
                    }
                    else if (cmd is AssignCmd)
                    {
                        AssignCmd assignCmd = (cmd as AssignCmd).AsSimpleAssignCmd;
                        Dictionary<Variable, Expr> map = new Dictionary<Variable, Expr>();
                        for (int k = 0; k < assignCmd.Lhss.Count; k++)
                        {
                            map[assignCmd.Lhss[k].DeepAssignedVariable] = assignCmd.Rhss[k];
                        }
                        Substitution subst = Substituter.SubstitutionFromHashtable(new Dictionary<Variable, Expr>());
                        Substitution oldSubst = Substituter.SubstitutionFromHashtable(map);
                        returnExpr = (Expr)new MySubstituter(subst, oldSubst).Visit(returnExpr);
                    }
                    else
                    {
                        Debug.Assert(false);
                    }
                }
            }
            return returnExpr;
        }

        private void Search(Block b, bool inFirst)
        {
            dfsStack.Push(b);
            if (b.TransferCmd is ReturnExprCmd)
            {
                if (first == null || inFirst)
                {
                    transitionRelation = Expr.Or(transitionRelation, CalculatePathCondition());
                }
                else
                {
                    Search(first.thisAction.Blocks[0], true);
                }
            }
            else
            {
                GotoCmd gotoCmd = b.TransferCmd as GotoCmd;
                foreach (Block target in gotoCmd.labelTargets)
                {
                    Search(target, inFirst);
                }
            }
            dfsStack.Pop();
        }
    }

}
