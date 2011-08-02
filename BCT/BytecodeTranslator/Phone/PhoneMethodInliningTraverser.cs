using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace BytecodeTranslator.Phone {
  public class PhoneMethodInliningMetadataTraverser : BaseMetadataTraverser {
    private HashSet<IMethodDefinition> methodsToInline;
    private HashSet<IMethodDefinition> iterMethodsToInline;
    private PhoneCodeHelper phoneHelper;
    private bool firstPassDone = false;
    private bool changedOnLastPass = false;
    private IAssemblyReference assemblyBeingTranslated;

    public PhoneMethodInliningMetadataTraverser(PhoneCodeHelper phoneHelper) {
      methodsToInline = new HashSet<IMethodDefinition>();
      iterMethodsToInline = new HashSet<IMethodDefinition>();
      this.phoneHelper = phoneHelper;
    }

    public override void Visit(IEnumerable<IModule> modules) {
      foreach (IModule module in modules) {
        assemblyBeingTranslated= module.ContainingAssembly;
        this.Visit(module);
      }
      firstPassDone = true;
    }

    public override void Visit(IMethodDefinition method) {
      if (iterMethodsToInline.Contains(method) || (!firstPassDone && phoneHelper.mustInlineMethod(method))) {
        PhoneMethodInliningCodeTraverser codeTraverser= new PhoneMethodInliningCodeTraverser();
        codeTraverser.Visit(method);
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
        Visit(modules);
      }
    }
  }

  class PhoneMethodInliningCodeTraverser : BaseCodeTraverser {
    private HashSet<IMethodDefinition> foundMethods = new HashSet<IMethodDefinition>();

    public override void Visit(IMethodCall methodCall) {
      foundMethods.Add(methodCall.MethodToCall.ResolvedMethod);
    }

    public IEnumerable<IMethodDefinition> getMethodsFound() {
      return foundMethods;
    }
  }
}
