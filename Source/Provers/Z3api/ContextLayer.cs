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

        public void SetModelCompletion(bool enabled)
        {
            config.SetParamValue("MODEL_VALUE_COMPLETION", (enabled ? "true" : "false"));
        }

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

    public abstract class Z3TermAst { }
    public abstract class Z3PatternAst { }
    public abstract class Z3ConstDeclAst { }
    public abstract class Z3LabeledLiterals { }

    public interface Z3Context
    {
        void CreateBacktrackPoint();
        void Backtrack();
        void AddAxiom(VCExpr axiom, LineariserOptions linOptions);
        void AddConjecture(VCExpr vc, LineariserOptions linOptions);
        void AddSmtlibString(string smtlibString);
        string GetDeclName(Z3ConstDeclAst constDeclAst);
        Z3PatternAst MakePattern(List<Z3TermAst> exprs);
        Z3TermAst MakeQuantifier(bool isForall, uint weight, string qid, int skolemid, List<string> varNames, List<Type> boogieTypes, List<Z3PatternAst> patterns, List<Z3TermAst> no_patterns, Z3TermAst body);
        ProverInterface.Outcome Check(out List<Z3ErrorModelAndLabels> boogieErrors);
        void TypeCheckBool(Z3TermAst t);
        void TypeCheckInt(Z3TermAst t);
        void DeclareType(string typeName);
        void DeclareConstant(string constantName, Type boogieType);
        void DeclareFunction(string functionName, List<Type> domain, Type range);
        Z3TermAst GetConstant(string constantName, Type constantType);
        Z3TermAst MakeIntLiteral(string numeral);
        Z3TermAst MakeTrue();
        Z3TermAst MakeFalse();
        Z3TermAst MakeLabel(string labelName, bool pos, Z3TermAst child);
        Z3LabeledLiterals GetRelevantLabels();
        Z3TermAst Make(string op, List<Z3TermAst> children);
        Z3TermAst MakeArraySelect(List<Z3TermAst> args);
        Z3TermAst MakeArrayStore(List<Z3TermAst> args);
    }

    internal class PartitionMap
    {
        private Context ctx;
        private Dictionary<Term, int> termToPartition = new Dictionary<Term, int>();
        private Dictionary<object, int> valueToPartition = new Dictionary<object, int>();
        private List<Object> partitionToValue = new List<Object>();
        private int partitionCounter = 0;
        public int PartitionCounter { get { return partitionCounter; } }

        public PartitionMap(Context ctx)
        { 
            this.ctx = ctx; 
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
            else if (s.Equals(intSort))
            {
                int i;
                if (ctx.TryGetNumeralInt(v, out i))
                {
                    return BigNum.FromInt(i);
                }
                else
                {
                    return BigNum.FromString(ctx.GetNumeralString(v));
                }
            }
            else if (ctx.TryGetArrayValue(v, out av))
            {
                List<List<int>> arrayValue = new List<List<int>>();
                List<int> tuple;
                for (int i = 0; i < av.Domain.Length; i++)
                {
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
            else
            {
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

        public BoogieErrorModelBuilder(Z3Context container)
        {
            this.container = container;
            this.partitionMap = new PartitionMap(((Z3SafeContext)container).z3);
        }
        
        private Dictionary<string, int> CreateConstantToPartition(Model z3Model)
        {
            Dictionary<string, int> constantToPartition = new Dictionary<string, int>();
            foreach (FuncDecl c in z3Model.GetModelConstants())
            {
                string name = container.GetDeclName(new Z3TypeSafeConstDecl(c));
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
                string f_name = container.GetDeclName(new Z3TypeSafeConstDecl(kv.Key));
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
            List<Object> partitionToValue = partitionMap.PartitionToValue(((Z3SafeContext)container).z3);
            Dictionary<object, int> valueToPartition = partitionMap.ValueToPartition(((Z3SafeContext)container).z3);
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
}