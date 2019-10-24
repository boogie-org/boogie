using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
    public class WitnessFunction
    {
        public enum InputArgumentKind
        {
            PRE_STATE,
            POST_STATE,
            FIRST_ARG,
            SECOND_ARG
        }

        public struct InputArgument
        {
            public readonly InputArgumentKind Kind;
            public readonly string Name;

            public InputArgument(InputArgumentKind kind, string name)
            {
                this.Kind = kind;
                this.Name = name;
            }
        }

        public readonly Function function;
        public readonly GlobalVariable globalVar;
        public readonly AtomicAction firstAction;
        public readonly AtomicAction secondAction;
        public readonly List<int> layers;
        public List<InputArgument> InputArgs { get; private set; }

        public WitnessFunction(Function function, GlobalVariable globalVar,
            AtomicAction firstAction, AtomicAction secondAction, List<int> layers)
        {
            this.function = function;
            this.globalVar = globalVar;
            this.firstAction = firstAction;
            this.secondAction = secondAction;
            this.layers = layers;
            this.InputArgs = new List<InputArgument>();
        }

        internal void AddInputMap(InputArgumentKind argumentKind, string name)
        {
            InputArgs.Add(new InputArgument(argumentKind, name));
        }
    }

    class WitnessFunctionVisitor : ReadOnlyVisitor
    {
        private readonly CivlTypeChecker ctc;
        internal List<WitnessFunction> allWitnessFunctions;

        public WitnessFunctionVisitor(CivlTypeChecker ctc)
        {
            this.ctc = ctc;
            allWitnessFunctions = new List<WitnessFunction>();
        }

        public override Function VisitFunction(Function node)
        {
            for (QKeyValue kv = node.Attributes; kv != null; kv = kv.Next)
            {
                if (kv.Key != CivlAttributes.WITNESS)
                    continue;
                if (kv.Params.Count == 1 && kv.Params[0] is string witnessAttribute)
                {
                    int parserErrorCount = WitnessAttributeParser.Parse(ctc, node, witnessAttribute,
                        out WitnessFunction witnessFunction);
                    if (parserErrorCount == 0 &&
                        WitnessFunctionChecker.Check(node, ctc, witnessFunction) == 0)
                    {
                        allWitnessFunctions.Add(witnessFunction);
                    }
                }
                else
                {
                    ctc.Error(node, "Witness attribute has to be a string.");
                }
            }
            return base.VisitFunction(node);
        }

        private class WitnessFunctionChecker
        {
            // TODO: Move these to a better place
            private const string FirstProcInputPrefix = "first_";
            private const string SecondProcInputPrefix = "second_";
            private const string PostStateSuffix = "'";
            private readonly Function node;
            private readonly CivlTypeChecker ctc;
            private readonly WitnessFunction witnessFunction;

            private int errorCount;

            private WitnessFunctionChecker(Function node, CivlTypeChecker ctc, WitnessFunction witnessFunction)
            {
                this.node = node;
                this.ctc = ctc;
                this.witnessFunction = witnessFunction;
                this.errorCount = 0;
                Check();
            }

            internal static int Check(Function node, CivlTypeChecker ctc, WitnessFunction witnessFunction)
            {
                var checker = new WitnessFunctionChecker(node, ctc, witnessFunction);
                return checker.errorCount;
            }

            private void Check()
            {
                CheckOutputVariable();
                CheckAtomicActionsLayers();
                CheckArguments();
            }

            private void CheckAtomicActionsLayers()
            {
                AtomicAction[] actions = { witnessFunction.firstAction, witnessFunction.secondAction };
                foreach (var action in actions)
                {
                    CheckLayerExistence(action.layerRange, action.proc.Name);
                }
            }

            private void CheckLayerExistence(LayerRange layerRange, string nodeName)
            {
                foreach (int layer in witnessFunction.layers)
                {
                    if (!layerRange.Contains(layer))
                    {
                        Error(string.Format("{0} does not exist at layer {1}", nodeName, layer));
                    }
                }
            }

            private void CheckOutputVariable()
            {
                if (node.OutParams.Count != 1)
                {
                    Error("Witness functions must have only one output");
                    return;
                }
                var v = witnessFunction.globalVar;
                CheckGlobalArg(v.TypedIdent.Type, v.Name);
            }

            private void CheckArguments()
            {
                for (int k = 0; k < node.InParams.Count; k++)
                {
                    var arg = node.InParams[k];
                    string name = node.InParams[k].Name;
                    Type type = arg.TypedIdent.Type;
                    WitnessFunction.InputArgumentKind argumentKind;
                    if (name.StartsWith(FirstProcInputPrefix, StringComparison.Ordinal))
                    {
                        name = name.Substring(FirstProcInputPrefix.Length);
                        argumentKind = WitnessFunction.InputArgumentKind.FIRST_ARG;
                        CheckArg(witnessFunction.firstAction, type, name);
                    }
                    else if (name.StartsWith(SecondProcInputPrefix, StringComparison.Ordinal))
                    {
                        name = name.Substring(SecondProcInputPrefix.Length);
                        argumentKind = WitnessFunction.InputArgumentKind.SECOND_ARG;
                        CheckArg(witnessFunction.secondAction, type, name);
                    }
                    else
                    {
                        if (name.EndsWith(PostStateSuffix, StringComparison.Ordinal))
                        {
                            name = name.Substring(0, name.Length - 1);
                            argumentKind = WitnessFunction.InputArgumentKind.POST_STATE;
                        }
                        else
                        {
                            argumentKind = WitnessFunction.InputArgumentKind.PRE_STATE;
                        }
                        CheckGlobalArg(type, name);
                    }
                    witnessFunction.AddInputMap(argumentKind, name);
                }
            }

            private void CheckGlobalArg(Type type, string name)
            {
                GlobalVariable globalVar = ctc.sharedVariables.Find(v => v.Name == name);
                if (globalVar is null)
                {
                    Error("No matching global variable named " + name);
                    return;
                }

                var gType = globalVar.TypedIdent.Type;
                if (!type.Equals(gType))
                {
                    Error(string.Format(
                        "Type mismatch for variable {0}. Expected {1} found {2}",
                        name, gType, type));
                }
                CheckLayerExistence(ctc.GlobalVariableLayerRange(globalVar), globalVar.Name);
            }

            private void CheckArg(AtomicAction action, Type type, string name)
            {
                var proc = action.proc;
                var v = proc.InParams.Union(proc.OutParams).
                    FirstOrDefault(i => i.Name == name && i.TypedIdent.Type.Equals(type));
                if (v is null)
                {
                    Error(string.Format("No parameter {0}:{1} found in {2}",
                        name, type, action.proc.Name));
                }
            }

            private void Error(string msg)
            {
                ctc.Error(node, msg);
                errorCount++;
            }
        }

        private class WitnessAttributeParser
        {
            private readonly CivlTypeChecker ctc;
            private readonly Function node;
            private readonly string[] parts;

            internal GlobalVariable globalVar;
            internal AtomicAction firstAction;
            internal AtomicAction secondAction;
            internal List<int> layers;

            private int parseIndex;
            private string ld;

            private int errorCount;

            private WitnessAttributeParser(CivlTypeChecker ctc, Function node, string witnessAttr)
            {
                this.ctc = ctc;
                this.node = node;

                char[] separators = { ' ', '\t' };
                parts = witnessAttr.Split(separators,
                    StringSplitOptions.RemoveEmptyEntries);

                this.parseIndex = 0;
                this.errorCount = 0;
                Parse();
            }

            internal static int Parse(CivlTypeChecker ctc, Function node, string witnessAttr,
                out WitnessFunction witnessFunction)
            {
                var parser = new WitnessAttributeParser(ctc, node, witnessAttr);
                witnessFunction = new WitnessFunction(node, parser.globalVar,
                    parser.firstAction, parser.secondAction, parser.layers);
                return parser.errorCount;
            }

            private void Parse()
            {
                ParseGlobalVar();
                ParseProc(out firstAction);
                ParseProc(out secondAction);
                ParseLayers();
                Debug.Assert(!TryNext());
            }

            private bool TryNext(string msg = null)
            {
                if (parseIndex >= parts.Length)
                {
                    if (msg != null) { Error(msg); }
                    ld = null;
                    return false;
                }
                ld = parts[parseIndex++];
                return true;
            }

            private void ParseLayers()
            {
                layers = new List<int>();
                if (TryNext("Expected layer number"))
                {
                    do
                    {
                        AddLayer();
                    } while (TryNext());
                }
            }

            private void AddLayer()
            {
                if (int.TryParse(ld, out int layerNum))
                {
                    layers.Add(layerNum);
                }
                else
                {
                    Error(string.Format("Expected integer layer number but received {0}", ld));
                }
            }

            private void ParseProc(out AtomicAction action)
            {
                TryNext("Expected procedure name.");
                Procedure proc = ctc.program.FindProcedure(ld);
                if (proc is null)
                {
                    Error("No procedure found with name of " + ld);
                    action = null;
                }
                else
                {
                    if (!ctc.procToAtomicAction.ContainsKey(proc))
                    {
                        ctc.checkingContext.Warning(node,
                            string.Format(
                                "Procedure {0} does not have a mover type, witness function is ignored.",
                                proc.Name));
                        // TODO: Add notes on this
                        errorCount++;
                        action = null;
                    }
                    else { action = ctc.procToAtomicAction[proc]; }
                }
            }

            private void ParseGlobalVar()
            {
                TryNext("Expected global variable name");
                globalVar = ctc.sharedVariables.Find(v => v.Name == ld);
                if (globalVar is null)
                {
                    Error("No global variable found with name of " + ld);
                }
            }

            private void Error(string msg)
            {
                ctc.Error(node, msg);
                errorCount++;
            }
        }
    }
}
