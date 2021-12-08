namespace Microsoft.Boogie
{
  class ConstantVisitor : DependencyEvaluator
  {
    protected ConstantVisitor(Declaration declaration) : base(declaration)
    {
    }
    
    public static DependencyEvaluator GetDependencies(Constant constant)
    {
      var result = new ConstantVisitor(constant);
      foreach (var definitionAxiom in constant.DefinitionAxioms) {
        result.AddOutgoing(definitionAxiom);
      }
      result.Visit(constant);
      return result;
    }
  }
}