using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.MutableCodeModel;

namespace BytecodeTranslator.Phone {
  class PhoneBackKeyCallbackTraverser : BaseCodeTraverser {
    private ITypeReference typeBeingTraversed;
    private IMetadataHost host;

    public PhoneBackKeyCallbackTraverser(IMetadataHost host) {
      this.host = host;
    }

    public override void Visit(ITypeDefinition typeDef) {
      typeBeingTraversed = typeDef;
      base.Visit(typeDef);
    }
    
    public override void Visit(IMethodCall methodCall) {
      if (methodCall.MethodToCall.ResolvedMethod.IsSpecialName && methodCall.MethodToCall.Name.Value == "add_BackKeyPress") {
        // check if it is a back key handler and if it is...
        // NAVIGATION TODO this only catches really locally delegate expressions. If it is created before, we see it as a BoundExpression
        // NAVIGATION TODO and need (again) data flow analysis
        bool delegateIsIdentified= false;
        bool delegateIsAnonymous = false;
        PhoneCodeHelper.instance().OnBackKeyPressOverriden = true;
        IBlockStatement delegateBody = null;
        IMethodDefinition delegateMethodRef= null;
        if (methodCall.Arguments.Count() == 1) {
          IExpression delegateArg= methodCall.Arguments.First();
          ICreateDelegateInstance localDelegate = delegateArg as ICreateDelegateInstance;
          if (localDelegate != null) {
            delegateIsIdentified = true;
            delegateMethodRef = localDelegate.MethodToCallViaDelegate.ResolvedMethod;
            SourceMethodBody body= delegateMethodRef.Body as SourceMethodBody;
            if (body != null)
              delegateBody = body.Block;

            PhoneCodeHelper.instance().KnownBackKeyHandlers.Add(delegateMethodRef);
          }

          AnonymousDelegate anonDelegate = delegateArg as AnonymousDelegate;
          if (anonDelegate != null) {
            delegateIsIdentified = true;
            delegateIsAnonymous = true;
            delegateBody = anonDelegate.Body;
          }

          // NAVIGATION TODO look for reachable method calls

          // NAVIGATION TODO what if it has no body?
          if (delegateBody != null) {
            bool navigates= false, cancelsNav= false;
            ICollection<string> navTargets;
            parseBlockForNavigation(delegateBody, out navigates, out navTargets);
            if (navigates) {
              ICollection<Tuple<IMethodReference,string>> targets = null;
              if (!PhoneCodeHelper.instance().BackKeyNavigatingOffenders.TryGetValue(typeBeingTraversed, out targets)) {
                targets = new HashSet<Tuple<IMethodReference,string>>();
              }

              foreach (string tgt in navTargets) {
                IMethodReference dummyRef=null;
                if (delegateIsAnonymous) {
                  dummyRef = new Microsoft.Cci.MutableCodeModel.MethodReference();
                  (dummyRef as Microsoft.Cci.MutableCodeModel.MethodReference).ContainingType= typeBeingTraversed;
                  (dummyRef as Microsoft.Cci.MutableCodeModel.MethodReference).Name = Dummy.Name;
                }
                targets.Add(Tuple.Create<IMethodReference, string>((delegateIsAnonymous ? dummyRef : delegateMethodRef), "\"" + tgt + "\""));
              }

              PhoneCodeHelper.instance().BackKeyNavigatingOffenders[typeBeingTraversed] = targets;
            }

            parseBlockForEventCancellation(delegateBody, out cancelsNav);
            if (cancelsNav) {
              string reason= "(via delegate ";
              if (delegateIsIdentified)
                reason += delegateMethodRef.ContainingType.ToString() + "." + delegateMethodRef.Name.Value;
              else
                reason += "anonymous";
              reason += ")";
              PhoneCodeHelper.instance().BackKeyCancellingOffenders.Add(Tuple.Create<ITypeReference,string>(typeBeingTraversed, reason));
            }
          }
        }

        if (!delegateIsIdentified) {
          PhoneCodeHelper.instance().BackKeyHandlerOverridenByUnknownDelegate = true;
          PhoneCodeHelper.instance().BackKeyUnknownDelegateOffenders.Add(typeBeingTraversed);
        }
      }
      base.Visit(methodCall);
    }

    private void parseBlockForNavigation(IBlockStatement block, out bool navigates, out ICollection<string> navTargets) {
      PhoneNavigationCallsTraverser traverser = new PhoneNavigationCallsTraverser(host);
      traverser.Visit(block);
      navigates = traverser.CodeDoesNavigation;
      navTargets = traverser.NavigationTargets;
    }

    private void parseBlockForEventCancellation(IBlockStatement block, out bool cancels) {
      PhoneNavigationCallsTraverser traverser = new PhoneNavigationCallsTraverser(host);
      traverser.Visit(block);
      cancels = traverser.CancelsEvents;
    }
  }

  public class PhoneNavigationCallsTraverser : BaseCodeTraverser {
    private IMetadataHost host;

    public bool CancelsEvents { get; private set; }
    public bool CodeDoesNavigation { get; private set; }
    public ICollection<string> NavigationTargets { get; private set; }
    public PhoneNavigationCallsTraverser(IMetadataHost host) {
      CancelsEvents = CodeDoesNavigation = false;
      NavigationTargets = new HashSet<string>();
      this.host = host;
    }

    public override void Visit(IMethodCall call) {
      checkMethodCallForEventCancellation(call);
      checkMethodCallForNavigation(call);
    }

    private void checkMethodCallForEventCancellation(IMethodCall call) {
      // NAVIGATION TODO this code is duplicated from PhoneNavigationTraverser, refactor that
      if (!call.MethodToCall.Name.Value.StartsWith("set_Cancel"))
        return;

      if (call.Arguments.Count() != 1 || call.Arguments.ToList()[0].Type != host.PlatformType.SystemBoolean)
        return;

      ICompileTimeConstant constant = call.Arguments.ToList()[0] as ICompileTimeConstant;
      if (constant != null && constant.Value != null) {
        CompileTimeConstant falseConstant = new CompileTimeConstant() {
          Type = host.PlatformType.SystemBoolean,
          Value = false,
        };
        if (constant.Value == falseConstant.Value)
          return;
      }

      CancelsEvents = true;
    }

    private void checkMethodCallForNavigation(IMethodCall call) {
      // NAVIGATION TODO this code is duplicated from PhoneNavigationTraverser, refactor that
      string targetUri = null;
      if (!call.MethodToCall.ContainingType.isNavigationServiceClass(host))
        return;

      if (!PhoneCodeHelper.NAV_CALLS.Contains(call.MethodToCall.Name.Value) || call.MethodToCall.Name.Value == "GoBack") // back is actually ok
        return;

      if (call.MethodToCall.Name.Value == "Navigate") {
        try {
          IExpression expr = call.Arguments.First();
          bool isStatic = UriHelper.isArgumentURILocallyCreatedStatic(expr, host, out targetUri) ||
                         UriHelper.isArgumentURILocallyCreatedStaticRoot(expr, host, out targetUri);
          if (!isStatic)
            targetUri = "--Other non inferrable target--";
          else
            targetUri = UriHelper.getURIBase(targetUri);
        } catch (InvalidOperationException) {
        }
      }
      CodeDoesNavigation= true;
      NavigationTargets.Add(targetUri);
    }
  }
}
