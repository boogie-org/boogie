using System;
using Microsoft.Boogie;

namespace Microsoft.Boogie
{
    public class CivlUtil
    {
        public static void AddInlineAttribute(Declaration decl)
        {
            decl.AddAttribute("inline", new LiteralExpr(Token.NoToken, Microsoft.Basetypes.BigNum.FromInt(1)));
        }
    }
}
