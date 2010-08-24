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
        void AddAxiom(VCExpr vc, LineariserOptions linOptions);
        void AddConjecture(VCExpr vc, LineariserOptions linOptions);
        void AddSmtlibString(string smtlibString);
        string GetDeclName(Z3ConstDeclAst constDeclAst);
        Z3PatternAst MakePattern(List<Z3TermAst> exprs);
        Z3TermAst MakeForall(uint weight, List<string> varNames, List<Type> boogieTypes, List<Z3PatternAst> patterns, List<Z3TermAst> no_patterns, Z3TermAst body);
        Z3TermAst MakeExists(uint weight, List<string> varNames, List<Type> boogieTypes, List<Z3PatternAst> patterns, List<Z3TermAst> no_patterns, Z3TermAst body);
        List<string> BuildConflictClause(Z3LabeledLiterals relevantLabels);
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
        private Dictionary<int, int> partitionToValueHash = new Dictionary<int, int>();
        private int partitionCounter = FAKE_PARTITION;
        public int GetPartition(int valueHash)
        {
            if (!partitionToValueHash.ContainsKey(valueHash))
            {
                partitionCounter++;
                partitionToValueHash.Add(valueHash, partitionCounter);
            }
            int partition;
            partitionToValueHash.TryGetValue(valueHash, out partition);
            return partition;
        }
        public int GetPartitionCount()
        {
            return partitionCounter + 1;
        }

        private const int FAKE_PARTITION = 0;
        public int GetFakePartition()
        {
            return FAKE_PARTITION;
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
            this.partitionMap = new PartitionMap();
        }

        private Dictionary<string, object> CreateConstantToValue(Model z3Model)
        {
            Dictionary<string, object> constantToValue = new Dictionary<string, object>();
            foreach (FuncDecl c in z3Model.GetModelConstants())
            {
                string c_name = container.GetDeclName(new Z3TypeSafeConstDecl(c));
                Term v = z3Model.Eval(c, new Term[0]);
                Sort s = v.GetSort();
                Context ctx = ((Z3SafeContext)container).z3;
                Sort boolSort = ctx.MkBoolSort();
                Sort intSort = ctx.MkIntSort();

                if (s == boolSort)
                {
                    constantToValue.Add(c_name, ctx.GetBoolValue(v));
                }
                else if (s == intSort)
                {
                    int i;
                    if (ctx.TryGetNumeralInt(v, out i))
                        constantToValue.Add(c_name, i);
                    // TBD: 
                    // ctx.GetNumeralValueString(v)?
                }
                else
                {
                    constantToValue.Add(c_name, null);
                }
            }
            return constantToValue;
        }

        private Dictionary<string, int> CreateConstantToPartition(Model z3Model)
        {
            Dictionary<string, int> constantToPartition = new Dictionary<string, int>();
            foreach (FuncDecl c in z3Model.GetModelConstants())
            {
                string c_name = container.GetDeclName(new Z3TypeSafeConstDecl(c));
                constantToPartition.Add(c_name, partitionMap.GetPartition(z3Model.Eval(c, new Term[0]).GetHashCode()));
            }
            return constantToPartition;
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
                        tuple.Add(partitionMap.GetPartition(z3Model.Eval(v).GetHashCode()));
                    }
                    tuple.Add(partitionMap.GetPartition(z3Model.Eval(entry.Result).GetHashCode()));
                    f_tuples.Add(tuple);
                }
                List<int> else_tuple = new List<int>();
                else_tuple.Add(partitionMap.GetPartition(z3Model.Eval(graph.Else).GetHashCode()));
                f_tuples.Add(else_tuple);
                functionToPartition.Add(f_name, f_tuples);
            }
            return functionToPartition;
        }

        private List<List<string>> ReverseConstantToPartition(Dictionary<string, int> map, int partitionCount)
        {
            List<string>[] reverse = new List<string>[partitionCount];
            foreach (KeyValuePair<string, int> entry in map)
            {
                List<string> v = reverse[entry.Value];
                if (v == null)
                {
                    v = new List<string>();
                    reverse[entry.Value] = v;
                }
                v.Add(entry.Key);
            }

            List<List<string>> result = new List<List<string>>();
            for (int i = 0; i < reverse.Length; i++)
            {
                if (reverse[i] == null)
                    result.Add(new List<string>());
                else
                    result.Add(reverse[i]);
            }
            return result;
        }

        private List<Object> CreatePartitionToValue(Dictionary<string, int> constantToPartition, Dictionary<string, object> constantToValue, int partitionCount)
        {
            Object[] partitionToValue = new Object[partitionCount];
            foreach (string constantName in constantToValue.Keys)
            {
                int partition;
                object objectValue;
                constantToPartition.TryGetValue(constantName, out partition);
                constantToValue.TryGetValue(constantName, out objectValue);
                partitionToValue[partition] = objectValue;
            }
            List<Object> result = new List<Object>();
            for (int j = 0; j < partitionToValue.Length; j++)
            {
                result.Add(partitionToValue[j]);
            }
            return result;
        }

        private Dictionary<object, int> CreateValueToPartition(Model z3Model)
        {
            // TODO Implement this method
            return new Dictionary<object, int>();
        }

        public Z3ErrorModel BuildBoogieModel(Model z3Model)
        {
            partitionMap = new PartitionMap();

            Dictionary<string, int> constantToPartition = CreateConstantToPartition(z3Model);
            Dictionary<string, object> constantToValue = CreateConstantToValue(z3Model);
            Dictionary<string, List<List<int>>> functionToPartition = CreateFunctionToPartition(z3Model);
            Dictionary<object, int> valueToPartition = CreateValueToPartition(z3Model);

            int partitionCount = partitionMap.GetPartitionCount();
            List<List<string>> partitionToConstant = ReverseConstantToPartition(constantToPartition, partitionCount);
            List<Object> partitionToValue = CreatePartitionToValue(constantToPartition, constantToValue, partitionCount);

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