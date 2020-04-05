using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Boogie
{
    interface NoninterferenceInstrumentation
    {
        List<Variable> NewLocalVars { get; }
        List<Cmd> CreateInitCmds(Implementation impl);
        List<Cmd> CreateUpdatesToPermissionCollector(Absy absy);
        List<Cmd> CreateCallToYieldProc();
    }
    
    class NoneNoninterferenceInstrumentation : NoninterferenceInstrumentation
    {
        public List<Variable> NewLocalVars => new List<Variable>();
        
        public List<Cmd> CreateInitCmds(Implementation impl)
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
        {
            return new List<Cmd>();
        }

        public List<Cmd> CreateCallToYieldProc()
        {
            return new List<Cmd>();
        }
    }

    class SomeNoninterferenceInstrumentation : NoninterferenceInstrumentation
    {
        private CivlTypeChecker civlTypeChecker;
        private LinearTypeChecker linearTypeChecker;
        private LinearPermissionInstrumentation linearPermissionInstrumentation;
        private Dictionary<Variable, Variable> oldGlobalMap;
        private Procedure yieldProc;

        private List<Variable> newLocalVars;
        private Dictionary<string, Variable> domainNameToHoleVar;
        
        public SomeNoninterferenceInstrumentation(
            CivlTypeChecker civlTypeChecker,
            LinearTypeChecker linearTypeChecker,
            LinearPermissionInstrumentation linearPermissionInstrumentation,
            Dictionary<Variable, Variable> oldGlobalMap,
            Procedure yieldProc)
        {
            this.civlTypeChecker = civlTypeChecker;
            this.linearTypeChecker = linearTypeChecker;
            this.linearPermissionInstrumentation = linearPermissionInstrumentation;
            this.oldGlobalMap = oldGlobalMap;
            this.yieldProc = yieldProc;
            this.newLocalVars = new List<Variable>();
            this.domainNameToHoleVar = new Dictionary<string, Variable>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                Variable l = linearTypeChecker.LinearDomainAvailableLocal(domainName);
                domainNameToHoleVar[domainName] = l;
                newLocalVars.Add(l);
            }
        }

        public List<Variable> NewLocalVars => newLocalVars;

        public List<Cmd> CreateInitCmds(Implementation impl)
        {
            Dictionary<string, Expr> domainNameToExpr = linearPermissionInstrumentation.PermissionExprs(impl);
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToHoleVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }
            var initCmds = new List<Cmd>();
            if (lhss.Count > 0)
            {
                initCmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
            return initCmds;
        }

        public List<Cmd> CreateUpdatesToPermissionCollector(Absy absy)
        {
            Dictionary<string, Expr> domainNameToExpr = linearPermissionInstrumentation.PermissionExprs(absy);
            List<AssignLhs> lhss = new List<AssignLhs>();
            List<Expr> rhss = new List<Expr>();
            foreach (var domainName in linearTypeChecker.linearDomains.Keys)
            {
                lhss.Add(new SimpleAssignLhs(Token.NoToken, Expr.Ident(domainNameToHoleVar[domainName])));
                rhss.Add(domainNameToExpr[domainName]);
            }
            var cmds = new List<Cmd>();
            if (lhss.Count > 0)
            {
                cmds.Add(new AssignCmd(Token.NoToken, lhss, rhss));
            }
            return cmds;
        }
        
        public List<Cmd> CreateCallToYieldProc()
        {
            List<Expr> exprSeq = new List<Expr>();
            foreach (string domainName in linearTypeChecker.linearDomains.Keys)
            {
                exprSeq.Add(Expr.Ident(domainNameToHoleVar[domainName]));
            }
            foreach (Variable g in civlTypeChecker.GlobalVariables)
            {
                exprSeq.Add(Expr.Ident(oldGlobalMap[g]));
            }
            CallCmd yieldCallCmd = new CallCmd(Token.NoToken, yieldProc.Name, exprSeq, new List<IdentifierExpr>());
            yieldCallCmd.Proc = yieldProc;
            return new List<Cmd> {yieldCallCmd};
        }
    }
}
