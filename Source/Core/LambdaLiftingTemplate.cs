using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie {

    /// <summary>
    /// Templates are used in the lambda lifting algorithm based on maximally large subexpressions not containing
    /// a lambda's bound variables (see <see cref="Core.MaxHolesLambdaLifter"/>).
    /// After the first phase of lambda lifting has been performed, each subexpression of a lambda is mapped to
    /// a template. A template is an expression that can have "holes" as subexpressions (holes are the maximally
    /// large subexpressions of a lambda that are free of bound variables and that will need to be lifted out of the
    /// lambda).
    /// Each template comes with a list of replacement expressions that indicate what each hole should be filled with
    /// (in other words, what is the original expression that is now replaced by a hole).
    ///
    /// We represent templates as follows:
    /// <list type="bullet">
    /// <item>
    ///     <description>No bound variables (hole)</description>
    ///         If a node does not have any bound variables, it is a hole.
    ///         This is represented using <see cref="TemplateNoBoundVariables"/>.
    ///         A hole has exactly one replacement expression.
    /// </item>
    /// <item>
    ///     <description>Contains bound variables (template with holes)</description>
    ///         If a node contains bound variables then it can have a (possibly empty, arbitrary-sized) list
    ///         of replacement expressions that indicate what the maximally large, bound-variable-free subexpressions
    ///         of the template are. 
    ///         This is represented using <see cref="TemplateWithBoundVariables"/>.
    /// </item>
    /// <item>
    ///     <description>No bound variables special case: trigger or attribute</description>
    ///         Since triggers and attributes are not considered expressions in the AST, but are instead
    ///         represented as linked lists that contain sequences of expressions, we must allow triggers and attributes
    ///         to contain a replacement for each expression sequence. We therefore define a special class
    ///         <see cref="TemplateNoBoundVariablesTriggerOrKv"/> that represents holes that can have multiple
    ///         replacements.
    /// </item>
    /// </list>
    /// </summary>
    public abstract class LambdaLiftingTemplate {

        protected readonly List<Expr> llReplacements;

        protected LambdaLiftingTemplate(List<Expr> llReplacements) {
            this.llReplacements = new List<Expr>(llReplacements);
        }
        
        public List<Expr> GetReplacements() {
            return llReplacements;
        }

        public abstract bool ContainsBoundVariables();
    }

    public class TemplateWithBoundVariables : LambdaLiftingTemplate {

        public TemplateWithBoundVariables(List<Expr> llReplacements) : base(llReplacements) {}

        public TemplateWithBoundVariables() : base(new List<Expr>()) { } // creating empty list so that we don't have to do null checks when concatenating lists

        public override bool ContainsBoundVariables() {
            return true;
        }
    }

    public class TemplateNoBoundVariables : LambdaLiftingTemplate {

        public TemplateNoBoundVariables(Expr llReplacement) : base(new List<Expr>() { llReplacement }) {}
        
        public Expr GetReplacement() {
            Contract.Requires(llReplacements.Count == 1);
            return llReplacements[0];
        }
        
        public override bool ContainsBoundVariables() {
            return false;
        }
    }

    public class TemplateNoBoundVariablesTriggerOrKv : LambdaLiftingTemplate {

        public TemplateNoBoundVariablesTriggerOrKv(List<Expr> llReplacements) : base(llReplacements) {}
        
        public override bool ContainsBoundVariables() {
            return false;
        }
    }
}