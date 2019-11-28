using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Boogie
{
    public class WitnessFunction
    {
        public readonly Function function;
        public readonly Variable witnessedVariable;
        public readonly AtomicAction firstAction;
        public readonly AtomicAction secondAction;
        public List<Expr> args;

        public WitnessFunction(Function function, Variable witnessedVariable,
            AtomicAction firstAction, AtomicAction secondAction, List<Expr> args)
        {
            this.function = function;
            this.witnessedVariable = witnessedVariable;
            this.firstAction = firstAction;
            this.secondAction = secondAction;
            this.args = args;
        }
    }

    class WitnessFunctionVisitor
    {
        private const string FirstProcInputPrefix = "first_";
        private const string SecondProcInputPrefix = "second_";
        private const string PostStateSuffix = "'";

        private readonly CivlTypeChecker ctc;
        internal List<WitnessFunction> allWitnessFunctions;

        private Variable witnessedVariable;
        private AtomicAction firstAction;
        private AtomicAction secondAction;
        private List<Expr> args;

        public WitnessFunctionVisitor(CivlTypeChecker ctc)
        {
            this.ctc = ctc;
            allWitnessFunctions = new List<WitnessFunction>();
        }

        public void VisitFunctions()
        {
            foreach (var f in ctc.program.Functions)
            {
                VisitFunction(f);
            }
        }

        private void VisitFunction(Function function)
        {
            Debug.Assert(function.OutParams.Count == 1);
            for (QKeyValue kv = function.Attributes; kv != null; kv = kv.Next)
            {
                if (kv.Key != CivlAttributes.WITNESS)
                    continue;
                if (kv.Params.Count == 3 &&
                    kv.Params[0] is string witnessedVariableName &&
                    kv.Params[1] is string firstActionName &&
                    kv.Params[2] is string secondActionName)
                {
                    witnessedVariable = ctc.sharedVariables.Find(v => v.Name == witnessedVariableName);
                    if (witnessedVariable == null)
                    {
                        ctc.Error(kv, $"Could not find shared variable {witnessedVariableName}");
                    }
                    else if (!function.OutParams[0].TypedIdent.Type.Equals(witnessedVariable.TypedIdent.Type))
                    {
                        ctc.Error(function, "Result type does not match witnessed variable");
                    }
                    firstAction = ctc.FindAtomicAction(firstActionName);
                    secondAction = ctc.FindAtomicAction(secondActionName);
                    if (firstAction == null)
                    {
                        ctc.Error(kv, $"Could not find atomic action {firstActionName}");
                    }
                    if (secondAction == null)
                    {
                        ctc.Error(kv, $"Could not find atomic action {firstActionName}");
                    }
                    if (firstAction != null && secondAction != null)
                    {
                        CheckInParams(function.InParams);
                    }
                    allWitnessFunctions.Add(new WitnessFunction(function, witnessedVariable,
                        firstAction, secondAction, args));
                }
                else
                {
                    ctc.Error(kv, "Witness attribute expects three string parameters");
                }
            }
        }

        private void CheckInParams(List<Variable> inParams)
        {
            args = new List<Expr>();
            foreach (var param in inParams)
            {
                Expr arg = null;
                if (param.Name.StartsWith(FirstProcInputPrefix, StringComparison.Ordinal))
                {
                    arg = CheckLocal(param, firstAction.firstImpl, FirstProcInputPrefix);
                }
                else if (param.Name.StartsWith(SecondProcInputPrefix, StringComparison.Ordinal))
                {
                    arg = CheckLocal(param, secondAction.secondImpl, SecondProcInputPrefix);
                }
                else
                {
                    arg = CheckGlobal(param);
                }
                args.Add(arg);
            }
        }

        private Expr CheckLocal(Variable param, Implementation impl, string prefix)
        {
            var var = FindVariable(param.Name, param.TypedIdent.Type,
                impl.InParams.Union(impl.OutParams));
            if (var != null)
                return Expr.Ident(var);
            var name = param.Name.Remove(0, prefix.Length);
            ctc.Error(param, $"Action {impl.Name} does not have parameter {name}:{param.TypedIdent.Type}");
            return null;
        }

        private Expr CheckGlobal(Variable param)
        {
            bool postState = param.Name.EndsWith(PostStateSuffix, StringComparison.Ordinal);
            var name = param.Name;
            if (postState)
                name = name.Substring(0, name.Length - 1);
            var var = FindVariable(name, param.TypedIdent.Type, ctc.sharedVariables);
            if (var != null)
            {
                if (!postState)
                    return ExprHelper.Old(Expr.Ident(var));
                else
                    return Expr.Ident(var);
            }
            ctc.Error(param, $"No shared variable {name}:{param.TypedIdent.Type}");
            return null;
        }

        private Variable FindVariable(string name, Type type, IEnumerable<Variable> vars)
        {
            return vars.FirstOrDefault(i => i.Name == name && i.TypedIdent.Type.Equals(type));
        }
    }
}
