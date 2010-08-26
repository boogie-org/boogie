using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Diagnostics;
using Microsoft.Contracts;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.Z3;
using Microsoft.Z3;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.Z3
{
    internal class Z3TypeSafeTerm : Z3TermAst
    {
        private Term termAst;
        public Z3TypeSafeTerm(Term termAst)
        {
            this.termAst = termAst;
        }
        public Term TermAst
        {
            get { return this.termAst; }
        }
    }

    internal class Z3TypeSafePattern : Z3PatternAst
    {
        private Pattern patternAst;
        public Z3TypeSafePattern(Pattern patternAst)
        {
            this.patternAst = patternAst;
        }
        public Pattern PatternAst
        {
            get { return this.patternAst; }
        }
    }

    internal class Z3TypeSafeConstDecl : Z3ConstDeclAst
    {
        private FuncDecl constDeclAst;
        public Z3TypeSafeConstDecl(FuncDecl constDeclAst)
        {
            this.constDeclAst = constDeclAst;
        }
        public FuncDecl ConstDeclAst
        {
            get { return this.constDeclAst; }
        }
    }

    public class Z3SafeType : Z3Type
    {
        private Sort typeAst;
        public Z3SafeType(Sort typeAst)
        {
            this.typeAst = typeAst;
        }
        public Sort TypeAst
        {
            get { return this.typeAst; }
        }
    }

    public class Z3SafeLabeledLiterals : Z3LabeledLiterals
    {
        private LabeledLiterals labeledLiterals;
        public Z3SafeLabeledLiterals(LabeledLiterals labeledLiterals)
        {
            this.labeledLiterals = labeledLiterals;
        }
        public LabeledLiterals LabeledLiterals
        {
            get { return this.labeledLiterals; }
        }
    }

    public class Z3SafeContext : Z3Context
    {
        private BacktrackDictionary<string, Symbol> symbols = new BacktrackDictionary<string, Symbol>();
        internal BacktrackDictionary<string, Z3TypeSafeTerm> constants = new BacktrackDictionary<string, Z3TypeSafeTerm>();
        internal BacktrackDictionary<string, Z3TypeSafeConstDecl> functions = new BacktrackDictionary<string, Z3TypeSafeConstDecl>();
        internal BacktrackDictionary<string, Z3TypeSafeTerm> labels = new BacktrackDictionary<string, Z3TypeSafeTerm>();

        public Context z3;
        public Z3Config config;
        public Z3apiProverContext ctxt;
        private VCExpressionGenerator gen;
        private Z3TypeCachedBuilder tm;
        private UniqueNamer namer;
        public UniqueNamer Namer
        {
            get { return namer; }
        }

        public Z3SafeContext(Z3apiProverContext ctxt, Z3Config config, VCExpressionGenerator gen)
        {
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
        }

        public void CreateBacktrackPoint()
        {
            symbols.CreateBacktrackPoint();
            constants.CreateBacktrackPoint();
            functions.CreateBacktrackPoint();
            labels.CreateBacktrackPoint();
            z3.Push();
        }

        public void Backtrack()
        {
            z3.Pop();
            labels.Backtrack();
            functions.Backtrack();
            constants.Backtrack();
            symbols.Backtrack();
        }

        public void AddAxiom(VCExpr axiom, LineariserOptions linOptions)
        {
            Z3apiExprLineariser visitor = new Z3apiExprLineariser(this, namer);
            Z3TermAst z3ast = (Z3TermAst)axiom.Accept(visitor, linOptions);
            Term term = Unwrap(z3ast);
            z3.AssertCnstr(term);
        }

        public void AddConjecture(VCExpr vc, LineariserOptions linOptions)
        {
            VCExpr not_vc = (VCExpr)this.gen.Not(vc);
            Z3apiExprLineariser visitor = new Z3apiExprLineariser(this, namer);
            Z3TermAst z3ast = (Z3TermAst)not_vc.Accept(visitor, linOptions);
            Term term = Unwrap(z3ast);
            z3.AssertCnstr(term);
        }

        public void AddSmtlibString(string smtlibString)
        {
            FuncDecl[] decls;
            Term[] assumptions;
            Term[] terms;
            Sort[] sorts;
            string tmp;

            z3.ParseSmtlibString(smtlibString, new Sort[] { }, new FuncDecl[] { },
                                 out assumptions, out terms, out decls, out sorts, out tmp);
            // TBD: check with Nikolaj about the correct position of assumptions
            foreach (FuncDecl decl in decls)
            {
                Symbol symbol = z3.GetDeclName(decl);
                string functionName = z3.GetSymbolString(symbol);
                functions.Add(functionName, new Z3TypeSafeConstDecl(decl));
            }
            foreach (Term assumption in assumptions)
            {
                z3.AssertCnstr(assumption);
            }
        }

        public string GetDeclName(Z3ConstDeclAst constDeclAst)
        {
            Z3TypeSafeConstDecl typeSafeConstDecl = (Z3TypeSafeConstDecl)constDeclAst;
            Symbol symbol = z3.GetDeclName(typeSafeConstDecl.ConstDeclAst);
            return z3.GetSymbolString(symbol);
        }

        private List<Term> Unwrap(List<Z3TermAst> terms)
        {
            List<Term> unwrap = new List<Term>();
            foreach (Z3TermAst term in terms)
            {
                Term unwrapTerm = Unwrap(term);
                unwrap.Add(unwrapTerm);
            }
            return unwrap;
        }

        private List<Pattern> Unwrap(List<Z3PatternAst> patterns)
        {
            List<Pattern> unwrap = new List<Pattern>();
            foreach (Z3PatternAst pattern in patterns)
            {
                Z3TypeSafePattern typeSafePattern = (Z3TypeSafePattern)pattern;
                unwrap.Add(typeSafePattern.PatternAst);
            }
            return unwrap;
        }

        private Sort Unwrap(Z3Type type)
        {
            Z3SafeType typeSafeTerm = (Z3SafeType)type;
            return typeSafeTerm.TypeAst;
        }

        private Term Unwrap(Z3TermAst term)
        {
            Z3TypeSafeTerm typeSafeTerm = (Z3TypeSafeTerm)term;
            return typeSafeTerm.TermAst;
        }

        private FuncDecl Unwrap(Z3ConstDeclAst constDeclAst)
        {
            Z3TypeSafeConstDecl typeSafeConstDecl = (Z3TypeSafeConstDecl)constDeclAst;
            return typeSafeConstDecl.ConstDeclAst;
        }

        private Z3TypeSafeTerm Wrap(Term term)
        {
            return new Z3TypeSafeTerm(term);
        }

        private Z3TypeSafeConstDecl Wrap(FuncDecl constDecl)
        {
            return new Z3TypeSafeConstDecl(constDecl);
        }

        private Z3TypeSafePattern Wrap(Pattern pattern)
        {
            return new Z3TypeSafePattern(pattern);
        }

        public Z3PatternAst MakePattern(List<Z3TermAst> exprs)
        {
            List<Term> unwrapExprs = Unwrap(exprs);
            Pattern pattern = z3.MkPattern(unwrapExprs.ToArray());
            Z3PatternAst wrapPattern = Wrap(pattern);
            return wrapPattern;
        }

        private List<Sort> GetTypes(List<Type> boogieTypes)
        {
            List<Sort> z3Types = new List<Sort>();
            foreach (Type boogieType in boogieTypes)
            {
                Z3Type type = tm.GetType(boogieType);
                Sort unwrapType = Unwrap(type);
                z3Types.Add(unwrapType);
            }
            return z3Types;
        }

        public Z3TermAst MakeForall(uint weight, List<string> varNames, List<Type> boogieTypes, List<Z3PatternAst> patterns, List<Z3TermAst> no_patterns, Z3TermAst body)
        {
            List<Pattern> unwrapPatterns = Unwrap(patterns);
            // List<Term> unwrapNoPatterns = Unwrap(no_patterns);
            // List<Sort> z3Types = GetTypes(boogieTypes);
            // List<Symbol> symbols = GetSymbols(varNames);
            Term unwrapBody = Unwrap(body);

            List<Term> bound = new List<Term>();
            for (int i = 0; i < varNames.Count; i++)
            {
                Z3TermAst t = GetConstant(varNames[i], boogieTypes[i]);
                bound.Add(Unwrap(t));
            }
            Term termAst = z3.MkForall(weight, bound.ToArray(), unwrapPatterns.ToArray(), unwrapBody);
            /*
            Term termAst = z3.MkQuantifier(true,
                             weight,
                             unwrapPatterns.ToArray(),
                             unwrapNoPatterns.ToArray(),
                             z3Types.ToArray(),
                             symbols.ToArray(),
                             unwrapBody);
            */
            return Wrap(termAst);
        }

        public Z3TermAst MakeExists(uint weight, List<string> varNames, List<Type> boogieTypes, List<Z3PatternAst> patterns, List<Z3TermAst> no_patterns, Z3TermAst body)
        {
            List<Pattern> unwrapPatterns = Unwrap(patterns);
            // List<Term> unwrapNoPatterns = Unwrap(no_patterns);
            // List<Sort> z3Types = GetTypes(boogieTypes);
            // List<Symbol> symbols = GetSymbols(varNames);
            Term unwrapBody = Unwrap(body);

            List<Term> bound = new List<Term>();
            for (int i = 0; i < varNames.Count; i++)
            {
                Z3TermAst t = GetConstant(varNames[i], boogieTypes[i]);
                bound.Add(Unwrap(t));
            }
            Term termAst = z3.MkExists(weight, bound.ToArray(), unwrapPatterns.ToArray(), unwrapBody);
            /*
            Term termAst = z3.MkQuantifier(false,
                                                  weight,
                                                  unwrapPatterns.ToArray(),
                                                  unwrapNoPatterns.ToArray(),
                                                  z3Types.ToArray(),
                                                  symbols.ToArray(),
                                                  unwrapBody);
            */ 
            return Wrap(termAst);
        }

        private static bool Equals(List<string> l, List<string> r)
        {
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

        public List<string> BuildConflictClause(Z3LabeledLiterals z3relevantLabels)
        {
            List<string> lbls = new List<string>();
            LabeledLiterals relevantLabels = ((Z3SafeLabeledLiterals)z3relevantLabels).LabeledLiterals;
            uint num_labels = relevantLabels.GetNumLabels();
            for (uint i = 0; i < num_labels; ++i)
            {
                Symbol sym = relevantLabels.GetLabel(i);
                string labelName = z3.GetSymbolString(sym);
                if (!labelName.StartsWith("@"))
                {
                    relevantLabels.Disable(i);
                }
                lbls.Add(labelName);
            }
            z3.BlockLiterals(relevantLabels);

            return lbls;
        }

        private Z3ErrorModelAndLabels BuildZ3ErrorModel(Model z3Model, List<string> relevantLabels)
        {
            BoogieErrorModelBuilder boogieErrorBuilder = new BoogieErrorModelBuilder(this);
            Z3ErrorModel boogieModel = boogieErrorBuilder.BuildBoogieModel(z3Model);
            return new Z3ErrorModelAndLabels(boogieModel, new List<string>(relevantLabels));
        }

        private void DisplayRelevantLabels(List<string> relevantLabels)
        {
            foreach (string labelName in relevantLabels)
            {
                System.Console.Write(labelName + ",");
            }
            System.Console.WriteLine("---");
        }

        public ProverInterface.Outcome Check(out List<Z3ErrorModelAndLabels> boogieErrors)
        {
            boogieErrors = new List<Z3ErrorModelAndLabels>();
            LBool outcome = LBool.Undef;
            z3.Push();
            while (boogieErrors.Count < this.config.Counterexamples)
            {
                Model z3Model;
                //System.Console.WriteLine("Check Begin");
                outcome = z3.CheckAndGetModel(out z3Model);
                //System.Console.WriteLine("Check End");
                if (outcome != LBool.False)
                {
                    Debug.Assert(z3Model != null);

                    LabeledLiterals labels = z3.GetRelevantLabels();
                    List<string> labelStrings = BuildConflictClause(new Z3SafeLabeledLiterals(labels));
                    boogieErrors.Add(BuildZ3ErrorModel(z3Model, labelStrings));
                    labels.Dispose();

                    if (z3Model != null)
                        z3Model.Dispose();
                }
                else
                    break;
            }
            z3.Pop();

            if (boogieErrors.Count > 0)
                return ProverInterface.Outcome.Invalid;
            else if (outcome == LBool.False)
                return ProverInterface.Outcome.Valid;
            else
            {
                Debug.Assert(outcome == LBool.Undef);
                return ProverInterface.Outcome.Undetermined;
            }
        }

        public void TypeCheckBool(Z3TermAst term)
        {
            Term unwrapTerm = Unwrap(term);
            bool boolType = z3.GetSort(unwrapTerm).Equals(z3.MkBoolSort());
            if (!boolType)
                throw new Exception("Failed Bool Typecheck");
        }

        public void TypeCheckInt(Z3TermAst term)
        {
            Term unwrapTerm = Unwrap(term);
            bool intType = z3.GetSort(unwrapTerm).Equals(z3.MkIntSort());
            if (!intType)
                throw new Exception("Failed Int Typecheck");
        }

        public void DeclareType(string typeName)
        {
        }

        public void DeclareConstant(string constantName, Type boogieType)
        {
            Symbol symbolAst = GetSymbol(constantName);
            Z3Type typeAst = tm.GetType(boogieType);
            Sort unwrapTypeAst = Unwrap(typeAst);

            Term constAst = z3.MkConst(symbolAst, unwrapTypeAst);
            constants.Add(constantName, Wrap(constAst));
        }

        public void DeclareFunction(string functionName, List<Type> domain, Type range)
        {
            Symbol symbolAst = GetSymbol(functionName);

            List<Sort> domainAst = new List<Sort>();
            foreach (Type domainType in domain)
            {
                Z3Type type = tm.GetType(domainType);
                Sort unwrapType = Unwrap(type);
                domainAst.Add(unwrapType);
            }
            Z3Type rangeAst = tm.GetType(range);
            Sort unwrapRangeAst = Unwrap(rangeAst);
            FuncDecl constDeclAst = z3.MkFuncDecl(symbolAst, domainAst.ToArray(), unwrapRangeAst);
            Z3TypeSafeConstDecl typeSafeConstDecl = Wrap(constDeclAst);
            functions.Add(functionName, typeSafeConstDecl);
        }

        private List<Symbol> GetSymbols(List<string> symbolNames)
        {
            List<Symbol> symbols = new List<Symbol>();
            foreach (string symbolName in symbolNames)
                symbols.Add(GetSymbol(symbolName));
            return symbols;
        }

        private Symbol GetSymbol(string symbolName)
        {
            if (!symbols.ContainsKey(symbolName))
            {
                Symbol symbolAst = z3.MkSymbol(symbolName);
                symbols.Add(symbolName, symbolAst);
            }
            Symbol result;
            if (!symbols.TryGetValue(symbolName, out result))
                throw new Exception("symbol " + symbolName + " is undefined");
            return result;
        }

        public Z3TermAst GetConstant(string constantName, Type constantType)
        {
            Z3TypeSafeTerm typeSafeTerm;
            if (!constants.ContainsKey(constantName))
                this.DeclareConstant(constantName, constantType);

            if (!constants.TryGetValue(constantName, out typeSafeTerm))
                throw new Exception("constant " + constantName + " is not defined");
            return typeSafeTerm;
        }

        public Z3TermAst MakeIntLiteral(string numeral)
        {
            Term term = z3.MkNumeral(numeral, z3.MkIntSort());
            Z3TypeSafeTerm typeSafeTerm = Wrap(term);
            return typeSafeTerm;
        }

        public Z3TermAst MakeTrue()
        {
            Term term = z3.MkTrue();
            Z3TypeSafeTerm typeSafeTerm = Wrap(term);
            return typeSafeTerm;
        }

        public Z3TermAst MakeFalse()
        {
            Term term = z3.MkFalse();
            Z3TypeSafeTerm typeSafeTerm = Wrap(term);
            return typeSafeTerm;
        }

        public Z3TermAst MakeLabel(string labelName, bool pos, Z3TermAst child)
        {
            Symbol labelSymbol = this.GetSymbol(labelName);
            Term unwrapChild = Unwrap(child);

            Term labeledExpr = z3.MkLabel(labelSymbol, pos, unwrapChild);

            Z3TypeSafeTerm wrapLabeledExpr = Wrap(labeledExpr);
            labels.Add(labelName, wrapLabeledExpr);
            return wrapLabeledExpr;
        }

        public Z3LabeledLiterals GetRelevantLabels()
        {
            Z3SafeLabeledLiterals safeLiterals = new Z3SafeLabeledLiterals(z3.GetRelevantLabels());
            return safeLiterals;
        }

        public Z3TermAst Make(string op, List<Z3TermAst> children)
        {
            Term[] unwrapChildren = Unwrap(children).ToArray();
            Term term;
            switch (op)
            {
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
                default:
                    {
                        FuncDecl f = GetFunction(op);
                        term = z3.MkApp(f, unwrapChildren);
                    }
                    break;
            }
            Z3TypeSafeTerm typeSafeTerm = Wrap(term);
            return typeSafeTerm;
        }

        private FuncDecl GetFunction(string functionName)
        {
            Z3TypeSafeConstDecl function;
            if (!functions.TryGetValue(functionName, out function))
                throw new Exception("function " + functionName + " is undefined");
            FuncDecl unwrapFunction = Unwrap(function);
            return unwrapFunction;
        }

        public Z3TermAst MakeArraySelect(List<Z3TermAst> args)
        {
            Term[] unwrapChildren = Unwrap(args).ToArray();
            return Wrap(z3.MkArraySelect(unwrapChildren[0], unwrapChildren[1]));
        }

        public Z3TermAst MakeArrayStore(List<Z3TermAst> args)
        {
            Term[] unwrapChildren = Unwrap(args).ToArray();
            return Wrap(z3.MkArrayStore(unwrapChildren[0], unwrapChildren[1], unwrapChildren[2]));
        }
    }
}