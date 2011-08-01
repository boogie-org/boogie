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

    public PhoneMethodInliningMetadataTraverser(PhoneCodeHelper phoneHelper) {
      methodsToInline = new HashSet<IMethodDefinition>();
      iterMethodsToInline = new HashSet<IMethodDefinition>();
      this.phoneHelper = phoneHelper;
    }

    public override void Visit(IEnumerable<IModule> modules) {
      base.Visit(modules);
      firstPassDone = true;
    }

    public override void Visit(IMethodDefinition method) {
      if (iterMethodsToInline.Contains(method) || (!firstPassDone && phoneHelper.mustInlineMethod(method))) {
        PhoneMethodInliningCodeTraverser codeTraverser= new PhoneMethodInliningCodeTraverser();
        codeTraverser.Visit(method);
        foreach (IMethodDefinition newMethodDef in codeTraverser.getMethodsFound()) {
          if (!methodsToInline.Contains(newMethodDef))
            iterMethodsToInline.Add(newMethodDef);
        }
        methodsToInline.Add(method);
        iterMethodsToInline.Remove(method);
      }
    }

    public IEnumerable<IMethodDefinition> getMethodsToInline() {
      return methodsToInline;
    }

    public bool isFinished() {
      return !iterMethodsToInline.Any();
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
