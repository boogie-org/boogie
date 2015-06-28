//-----------------------------------------------------------------------------
//
// Copyright (C) 2012 Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Term = Microsoft.Boogie.VCExprAST.VCExpr;
using FuncDecl = Microsoft.Boogie.VCExprAST.VCExprOp;
using Sort = Microsoft.Boogie.Type;
using Microsoft.Boogie.VCExprAST;


using Microsoft.Boogie.ExprExtensions;


namespace Microsoft.Boogie
{

    
    

    /** This class represents a relation post-fixed point (RPFP) problem as
     *  a "problem graph". The graph consists of Nodes and hyper-edges.
     * 
     * A node consists of
     * - Annotation, a symbolic relation
     * - Bound, a symbolic relation giving an upper bound on Annotation
     * 
     *
     * A hyper-edge consists of:
     *  - Children, a sequence of children Nodes,
     *  - F, a symbolic relational transformer,
     *  - Parent, a single parent Node.
     *  
     * The graph is "solved" when:
     * - For every Node n, n.Annotation subseteq n.Bound
     * - For every hyperedge e, e.F(e.Children.Annotation) subseteq e.Parent.Annotation
     * 
     * where, if x is a sequence of Nodes, x.Annotation is the sequences
     * of Annotations of the nodes in the sequence.
     * 
     * A symbolic Transformer consists of
     * - RelParams, a sequence of relational symbols
     * - IndParams, a sequence of individual symbols
     * - Formula, a formula over RelParams and IndParams
     * 
     * A Transformer t represents a function that takes sequence R of relations
     * and yields the relation lambda (t.Indparams). Formula(R/RelParams).
     * 
     * As a special case, a nullary Transformer (where RelParams is the empty sequence)
     * represents a fixed relation.
     * 
     * An RPFP consists of
     * - Nodes, a set of Nodes
     * - Edges, a set of hyper-edges
     * - Context, a prover context that contains formula AST's
     *  
     * Multiple RPFP's can use the same Context, but you should be careful
     * that only one RPFP asserts constraints in the context at any time. 
     * 
     *  */
    public class RPFP
    {
        /** Symbolic representation of a relational transformer */
        public class Transformer
        {
            public FuncDecl[] RelParams;
            public Term[] IndParams;
            public Term Formula;
            public RPFP owner;

            public Transformer Clone()
            {
                return (Transformer)this.MemberwiseClone();
            }
        }

        /** Create a symbolic transformer. */
        public Transformer CreateTransformer(FuncDecl[] _RelParams, Term[] _IndParams, Term _Formula)
            {
                Transformer t = new Transformer();
                t.RelParams = _RelParams;
                t.IndParams = _IndParams;
                t.Formula = _Formula;
                t.owner = this;
                return t;
            }

        /** Create a relation (nullary relational transformer) */
        public Transformer CreateRelation(Term[] _IndParams, Term _Formula)
        {
            return CreateTransformer(new FuncDecl[0], _IndParams, _Formula);
        }

        /** A node in the RPFP graph */
        public class Node
        {
            public FuncDecl Name;
            public Transformer Annotation;
            public Transformer Bound;
            public RPFP owner;
            public int number;
            public Edge Outgoing;
            public List<Edge> Incoming;
            public Term dual;
            public Node map;
        }

        /** Create a node in the graph. The input is a term R(v_1...v_n)
         *  where R is an arbitrary relational symbol and v_1...v_n are
         *  arbitary distinct variables. The names are only of mnemonic value,
         *  however, the number and type of arguments determine the type
         *  of the relation at this node. */

        public Node CreateNode(Term t)
        {
            Node n = new Node();
            // Microsoft.Boogie.VCExprAST.VCExprNAry tn = t as Microsoft.Boogie.VCExprAST.VCExprNAry;
            // Term[] _IndParams = tn.ToArray();
            Term[] _IndParams = t.GetAppArgs();
            FuncDecl Name = t.GetAppDecl();
            n.Annotation = CreateRelation(_IndParams,ctx.MkTrue());
            n.Bound = CreateRelation(_IndParams, ctx.MkTrue());
            n.owner = this;
            n.number = ++nodeCount;
            n.Name = Name; // just to have a unique name
            n.Incoming = new List<Edge>();
            return n;
        }

        /** Clone a node (can be from another graph).  */

        public Node CloneNode(Node old)
        {
            Node n = new Node();
            n.Annotation = old.Annotation.Clone();
            n.Bound = old.Bound.Clone();
            n.owner = this;
            n.number = ++nodeCount;
            n.Name = old.Name; // just to have a unique name
            n.Incoming = new List<Edge>();
            return n;
        }

        /** This class represents a hyper-edge in the RPFP graph */

        public class Edge
        {
            public Transformer F;
            public Node Parent;
            public Node[] Children;
            public RPFP owner;
            public int number;
            public Edge map;
            public HashSet<string> labels;
            internal Term dual;
            internal TermDict<Term> valuation;
        }

        
        /** Create a hyper-edge. */
        public Edge CreateEdge(Node _Parent, Transformer _F, Node[] _Children)
        {
            Edge e = new Edge();
            e.Parent = _Parent;
            e.F = _F;
            e.Children = _Children;
            e.owner = this;
            e.number = ++edgeCount;
            _Parent.Outgoing = e;
            foreach (var c in _Children)
                if(c != null)
                  c.Incoming.Add(e);
            return e;
        }

        /** Create an edge that lower-bounds its parent. */
        public Edge CreateLowerBoundEdge(Node _Parent)
        {
            return CreateEdge(_Parent, _Parent.Annotation, new RPFP.Node[0]);
        }

        
        

        /** Assert a background axiom. Background axioms can be used to provide the
         *  theory of auxilliary functions or relations. All symbols appearing in
         *  background axioms are considered global, and may appear in both transformer
         *  and relational solutions. Semantically, a solution to the RPFP gives
         *  an interpretation of the unknown relations for each interpretation of the
         *  auxilliary symbols that is consistent with the axioms. Axioms should be
         *  asserted before any calls to Push. They cannot be de-asserted by Pop. */

        public void AssertAxiom(Term t)
        {
            ctx.AddAxiom(t);
        }

        /** Do not call this. */

        public void RemoveAxiom(Term t)
        {
            ctx.RemoveAxiom(t);
        }

        /** Type of solve results */
        public enum LBool { False, True, Undef };
        

        /** Solve an RPFP graph. This means either strengthen the annotation
         *  so that the bound at the given root node is satisfied, or
         *  show that this cannot be done by giving a dual solution 
         *  (i.e., a counterexample). 
         *  
         * In the current implementation, this only works for graphs that
         * are:
         * - tree-like
         * 
         * - closed.
         * 
         * In a tree-like graph, every nod has out most one incoming and one out-going edge,
         * and there are no cycles. In a closed graph, every node has exactly one out-going
         * edge. This means that the leaves of the tree are all hyper-edges with no
         * children. Such an edge represents a relation (nullary transformer) and thus
         * a lower bound on its parent. The parameter root must be the root of this tree.
         * 
         * If Solve returns LBool.False, this indicates success. The annotation of the tree
         * has been updated to satisfy the upper bound at the root. 
         * 
         * If Solve returns LBool.True, this indicates a counterexample. For each edge,
         * you can then call Eval to determine the values of symbols in the transformer formula.
         * You can also call Empty on a node to determine if its value in the counterexample
         * is the empty relation.
         * 
         *    \param root The root of the tree
         *    \param persist Number of context pops through which result should persist 
         * 
         * 
        */

        public LBool Solve(Node root, int persist)
        {
            return LBool.False; // TODO
        }


        /** Dispose of the dual model (counterexample) if there is one. */

        public void DisposeDualModel()
        {
            // TODO dualModel = null;
        }


        /** Determines the value in the counterexample of a symbol occuring in the transformer formula of
         *  a given edge. */

        public Term Eval(Edge e, Term t)
        {
            if (e.valuation == null)
                e.valuation = new TermDict< Term>();
            if (e.valuation.ContainsKey(t))
                return e.valuation[t];
            return null; // TODO
        }

        /** Sets the value in the counterexample of a symbol occuring in the transformer formula of
         *  a given edge. */

        public void SetValue(Edge e, Term variable, Term value)
        {
            if (e.valuation == null)
                e.valuation = new TermDict< Term>(); 
            e.valuation.Add(variable, value);
        }


        /** Returns true if the given node is empty in the primal solution. For proecudure summaries,
         this means that the procedure is not called in the current counter-model. */

        public bool Empty(Node p)
        {
            return false; // TODO
        }

        /** Push a scope. Assertions made after Push can be undone by Pop. */

        public void Push()
        {
            stack.Push(new stack_entry());
            // TODO: do we need push/pop?
        }

        /** Pop a scope (see Push). Note, you cannot pop axioms. */

        public void Pop(int num_scopes)
        {
            //TODO ctx.Pop((uint)num_scopes);
            for (uint i = 0; i < num_scopes; i++)
            {
                stack_entry back = stack.Pop();
                foreach (var e in back.edges)
                    e.dual = null;
                foreach (var n in back.nodes)
                    n.dual = null;
            }
        }

        public Context ctx;

        public class LogicSolver  {
            public Context ctx;
        };

        public LogicSolver solver;

        static public LogicSolver CreateLogicSolver(Context _ctx){
            LogicSolver res = new LogicSolver();
            res.ctx = _ctx;
            return res;
        }

        /** This represents a conjecture that a given node is upper-boudned
            by bound. */
        public class Conjecture
        {
            public Node node;
            public Transformer bound;
        }

        /** This is a list of conjectures generated during solving. */

        public List<Conjecture> conjectures = new List<Conjecture>();

        /** Construct an RPFP graph with a given interpolating prover context. It is allowed to
            have multiple RPFP's use the same context, but you should never have teo RPFP's
            with the same conext asserting nodes or edges at the same time. Note, if you create
            axioms in one RPFP, them create a second RPFP with the same context, the second will
            inherit the axioms. 
         */

        public RPFP(LogicSolver slvr)
        {
            solver = slvr;
            ctx = slvr.ctx;
            stack = new Stack<stack_entry>();
            stack.Push(new stack_entry());
        }


        /** Convert an array of clauses to an RPFP. 
         */

        public void FromClauses(Term[] clauses){
            FuncDecl failName = ctx.MkFuncDecl("@Fail", ctx.MkBoolSort());
            foreach(var clause in clauses){
                Node foo = GetNodeFromClause(clause,failName);
                if(foo != null)
                    nodes.Add(foo);
            }
            foreach (var clause in clauses)
                edges.Add(GetEdgeFromClause(clause,failName));
        }

        
        // This returns a new FuncDel with same sort as top-level function
        // of term t, but with numeric suffix appended to name.

        private FuncDecl SuffixFuncDecl(Term t, int n)
        {
            var name = t.GetAppDecl().GetDeclName() + "_" + n.ToString();
            return ctx.MkFuncDecl(name, t.GetAppDecl());
        }

        // Collect the relational paremeters

        Dictionary<FuncDecl, Node> relationToNode = new Dictionary<FuncDecl, Node>();

        private Term CollectParamsRec(TermDict<Term> memo, Term t, List<FuncDecl> parms, List<RPFP.Node> nodes, Dictionary<Term, Term> done)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            if (t.GetKind() == TermKind.App)
            {
                var f = t.GetAppDecl();
                Node node;
                if (relationToNode.TryGetValue(f, out node))
                {
                    if (done.ContainsKey(t))
                        res = done[t];
                    else
                    {
                        f = SuffixFuncDecl(t, parms.Count);
                        parms.Add(f);
                        nodes.Add(node);
                        done.Add(t,res); // don't count same expression twice!
                    }
                }
                var args = t.GetAppArgs();
                args = args.Select(x => CollectParamsRec(memo, x, parms, nodes, done)).ToArray();
                res = ctx.CloneApp(t, args);
            } // TODO: handle quantifiers
            else
                res = t;
            memo.Add(t, res);
            return res;
        }

        private bool IsVariable(Term t)
        {
            // TODO: is this right?
            // return t.IsFunctionApp() && t.GetAppArgs().Length == 0;
            return t is VCExprVar && !(t is VCExprConstant);
        }

        private Edge GetEdgeFromClause(Term t, FuncDecl failName)
        {
            Term[] args = t.GetAppArgs();
            Term body = args[0];
            Term head = args[1];
            Term[] _IndParams;
            FuncDecl Name;
            if (head.IsFalse())
            {
                Name = failName;
                _IndParams = new Term[0];
            }
            else
            {
                _IndParams = head.GetAppArgs();
                Name = head.GetAppDecl();
            }
            for(int i = 0; i < _IndParams.Length; i++)
                if (!IsVariable(_IndParams[i]))
                {
                    Term v = ctx.MkConst("@a" + i.ToString(), _IndParams[i].GetSort());
                    body = ctx.MkAnd(body, ctx.MkEq(v, _IndParams[i]));
                    _IndParams[i] = v;
                }
            var relParams = new List<FuncDecl>();
            var nodeParams = new List<RPFP.Node>();
            var memo = new TermDict< Term>();
            var done = new Dictionary<Term, Term>(); // note this hashes on equality, not reference!
            body = CollectParamsRec(memo, body, relParams, nodeParams,done);
            Transformer F = CreateTransformer(relParams.ToArray(), _IndParams, body);
            Node parent = relationToNode[Name];
            return CreateEdge(parent, F, nodeParams.ToArray());
        }

        private Node GetNodeFromClause(Term t, FuncDecl failName)
        {
            Term[] args = t.GetAppArgs();
            Term body = args[0];
            Term head = args[1];
            FuncDecl Name;
            Term[] _IndParams;
            bool is_query = false;
            if (head.Equals(ctx.MkFalse()))
            {
                Name = failName;
                is_query = true;
                _IndParams = new Term[0];
            }
            else
            {
                Name = head.GetAppDecl();
                _IndParams = head.GetAppArgs();
            }
            if (relationToNode.ContainsKey(Name))
                return null;
            for (int i = 0; i < _IndParams.Length; i++)
                if (!IsVariable(_IndParams[i]))
                {
                    Term v = ctx.MkConst("@a" + i.ToString(), _IndParams[i].GetSort());
                    _IndParams[i] = v;
                }
            Term foo = ctx.MkApp(Name, _IndParams);
            Node node = CreateNode(foo);
            relationToNode[Name] = node;
            if (is_query)
                node.Bound = CreateRelation(new Term[0], ctx.MkFalse());
            return node;
        }

        /////////////////////////////////////////////////////////////////////////////////////////
        // Convert RPFP to Z3 rules
        /////////////////////////////////////////////////////////////////////////////////////////

        /** Get the Z3 rule corresponding to an edge */
         
        public Term GetRule(Edge edge)
        {
            Dictionary<FuncDecl, FuncDecl> predSubst = new Dictionary<FuncDecl, FuncDecl>();
            for (int i = 0; i < edge.Children.Length; i++)
                predSubst.Add(edge.F.RelParams[i], edge.Children[i].Name);
            Term body = SubstPreds(predSubst, edge.F.Formula);
            Term head = ctx.MkApp(edge.Parent.Name, edge.F.IndParams);
            var rule = BindVariables(ctx.MkImplies(body, head));
            rule = ctx.Letify(rule); // put in let bindings for theorem prover
            return rule;
        }

        /** Get the Z3 query corresponding to the conjunction of the node bounds. */

        public Term GetQuery()
        {
            List<Term> conjuncts = new List<Term>();
            foreach (var node in nodes)
            {
                if (node.Bound.Formula != ctx.MkTrue())
                    conjuncts.Add(ctx.MkImplies(ctx.MkApp(node.Name, node.Bound.IndParams), node.Bound.Formula));
            }
            Term query = ctx.MkNot(ctx.MkAnd(conjuncts.ToArray()));
            query = BindVariables(query,false); // bind variables existentially
            query = ctx.Letify(query); // put in let bindings for theorem prover
            return query;
        }

        private void CollectVariables(TermDict< bool> memo, Term t, List<Term> vars)
        {
            if (memo.ContainsKey(t))
                return;
            if (IsVariable(t))
                vars.Add(t);
            if (t.GetKind() == TermKind.App)
            {
                foreach (var s in t.GetAppArgs())
                    CollectVariables(memo, s, vars);
            }
            memo.Add(t, true);
        }

        private Term BindVariables(Term t, bool universal = true)
        {
            TermDict< bool> memo = new TermDict<bool>();
            List<Term> vars = new List<Term>();
            CollectVariables(memo,t,vars);
            return universal ? ctx.MkForall(vars.ToArray(), t) : ctx.MkExists(vars.ToArray(), t);
        }

        private Term SubstPredsRec(TermDict< Term> memo, Dictionary<FuncDecl,FuncDecl> subst, Term t)
        {
            Term res;
            if (memo.TryGetValue(t, out res))
                return res;
            if (t.GetKind() == TermKind.App)
            {
                var args = t.GetAppArgs();
                args = args.Select(x => SubstPredsRec(memo,subst,x)).ToArray();
                FuncDecl nf = null;
                var f = t.GetAppDecl();
                if (subst.TryGetValue(f, out nf))
                {
                    res = ctx.MkApp(nf, args);
                }
                else
                {
                    res = ctx.CloneApp(t, args);
                }
            } // TODO: handle quantifiers
            else
                res = t;
            memo.Add(t, res);
            return res;
        }

        private Term SubstPreds(Dictionary<FuncDecl, FuncDecl> subst, Term t)
        {
            TermDict< Term> memo = new TermDict< Term>();
            return SubstPredsRec(memo, subst, t);
        }

        /* Everything after here is private. */

        private class stack_entry
        {
            public List<Edge> edges = new List<Edge>();
            public List<Node> nodes = new List<Node>();
        };

        /** Set the model of the background theory used in a counterexample. */
        public void SetBackgroundModel(Model m)
        {
            dualModel = m;
        }

        /** Set the model of the background theory used in a counterexample. */
        public Model GetBackgroundModel()
        {
            return dualModel;
        }

        private int nodeCount = 0;
        private int edgeCount = 0;
        private Model dualModel;
        // private LabeledLiterals dualLabels;
        private Stack<stack_entry> stack;
        public List<Node> nodes = new List<Node>();
        public List<Edge> edges = new List<Edge>();

       
    }
}
