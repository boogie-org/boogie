using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace BytecodeTranslator.Phone {
  public class PhoneMethodInliningMetadataTraverser : MetadataTraverser {
    private HashSet<IMethodDefinition> methodsToInline;
    private HashSet<IMethodDefinition> iterMethodsToInline;
    private PhoneCodeHelper phoneHelper;
    private bool firstPassDone = false;
    private bool changedOnLastPass = false;
    private IAssemblyReference assemblyBeingTranslated;

    public int TotalMethodsCount { get; private set; }
    public int InlinedMethodsCount { get { return methodsToInline.Count(); } }

    public PhoneMethodInliningMetadataTraverser(PhoneCodeHelper phoneHelper) {
      methodsToInline = new HashSet<IMethodDefinition>();
      iterMethodsToInline = new HashSet<IMethodDefinition>();
      this.phoneHelper = phoneHelper;
      TotalMethodsCount = 0;
    }

    public override void TraverseChildren(IAssembly assembly) {
      foreach (IModule module in assembly.MemberModules) {
        assemblyBeingTranslated = module.ContainingAssembly;
        this.Traverse(module);
      }
      firstPassDone = true;
    }

    public override void TraverseChildren(IMethodDefinition method) {
      if (!firstPassDone)
        TotalMethodsCount++;

      if (iterMethodsToInline.Contains(method) || (!firstPassDone && phoneHelper.mustInlineMethod(method))) {
        PhoneMethodInliningCodeTraverser codeTraverser= new PhoneMethodInliningCodeTraverser();
        codeTraverser.TraverseChildren(method);
        foreach (IMethodDefinition newMethodDef in codeTraverser.getMethodsFound()) {
          bool isExtern = this.assemblyBeingTranslated != null &&
                          !TypeHelper.GetDefiningUnitReference(newMethodDef.ContainingType).UnitIdentity.Equals(this.assemblyBeingTranslated.UnitIdentity);
          if (!methodsToInline.Contains(newMethodDef) && !isExtern) {
            iterMethodsToInline.Add(newMethodDef);
            changedOnLastPass = true;
          }
        }
        methodsToInline.Add(method);
        iterMethodsToInline.Remove(method);
      }
    }

    public IEnumerable<IMethodDefinition> getMethodsToInline() {
      return methodsToInline;
    }

    public bool isFinished() {
      return firstPassDone && !changedOnLastPass;
    }

    public void findAllMethodsToInline(List<IModule> modules) {
      while (!isFinished()) {
        changedOnLastPass = false;
        this.Traverse(modules);
      }
    }
  }

  class PhoneMethodInliningCodeTraverser : CodeTraverser {
    private HashSet<IMethodDefinition> foundMethods = new HashSet<IMethodDefinition>();

    public override void TraverseChildren(IMethodCall methodCall) {
      foundMethods.Add(methodCall.MethodToCall.ResolvedMethod);
    }

    public IEnumerable<IMethodDefinition> getMethodsFound() {
      return foundMethods;
    }
  }
}
