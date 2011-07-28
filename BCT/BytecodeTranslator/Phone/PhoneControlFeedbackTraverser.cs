using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.MutableCodeModel;

namespace BytecodeTranslator.Phone {
  class PhoneControlFeedbackCodeTraverser : BaseCodeTraverser {
    private IMetadataReaderHost host;

    public PhoneControlFeedbackCodeTraverser(IMetadataReaderHost host) : base() {
      this.host = host;
    }

    public override void Visit(IMethodCall methodCall) {
      if (PhoneCodeHelper.instance().PhoneFeedbackToggled) {
        // check for handlers we do not wish to add feedback checks to
        if (methodCall.MethodToCall.Name.Value.StartsWith("add_")) {
          string eventName = methodCall.MethodToCall.Name.Value.Remove(0, "add_".Length);
          if (PhoneCodeHelper.IgnoredEvents.Contains(eventName)) {
            IMethodReference eventHandler = null;
            foreach (IExpression arg in methodCall.Arguments) {
              ICreateDelegateInstance createDelegate = arg as ICreateDelegateInstance;
              if (createDelegate == null)
                continue;

              ITypeReference typeRef = createDelegate.Type;
              if (!typeRef.isRoutedEventHandlerClass(host))
                continue;

              eventHandler = createDelegate.MethodToCallViaDelegate;
              break;
            }

            if (eventHandler != null) {
              INamespaceTypeReference namedType = eventHandler.ContainingType.ResolvedType as INamespaceTypeReference;
              if (namedType != null) {
                INamespaceTypeDefinition namedTypeDef = namedType.ResolvedType;
                if (namedTypeDef != null) {
                  PhoneCodeHelper.instance().ignoreEventHandler(namedTypeDef.ContainingUnitNamespace.Name + "." + namedTypeDef.Name + "." + eventHandler.Name);
                }
              }
            }
          }
        }
      }
    }

  }

  class PhoneControlFeedbackMetadataTraverser : BaseMetadataTraverser {
    private IMetadataReaderHost host;

    public PhoneControlFeedbackMetadataTraverser(IMetadataReaderHost host) : base() {
      this.host = host;
    }

    public override void Visit(IMethodDefinition method) {
      PhoneControlFeedbackCodeTraverser codeTraverser = new PhoneControlFeedbackCodeTraverser(host);
      codeTraverser.Visit(method);
    }
  }
}
