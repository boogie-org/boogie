using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Diagnostics;

namespace GPUVerify
{




    class ReadCollector : AccessCollector
    {

        public HashSet<AccessRecord> accesses = new HashSet<AccessRecord>();

        public ReadCollector(List<Variable> GlobalVariables, List<Variable> TileStaticVariables)
            : base(GlobalVariables, TileStaticVariables)
        {
        }

        public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
        {
            return node;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (node.Fun is MapSelect)
            {
                if ((node.Fun as MapSelect).Arity > 1)
                {
                    MultiDimensionalMapError();
                }

                Variable ReadVariable = null;
                Expr IndexX = node.Args[1];
                Expr IndexY = null;
                Expr IndexZ = null;

                if (node.Args[0] is NAryExpr)
                {
                    NAryExpr nestedMap = node.Args[0] as NAryExpr;
                    Debug.Assert(nestedMap.Fun is MapSelect);
                    if ((nestedMap.Fun as MapSelect).Arity > 1)
                    {
                        MultiDimensionalMapError();
                    }
                    IndexY = nestedMap.Args[1];
                    if (nestedMap.Args[0] is NAryExpr)
                    {
                        NAryExpr nestedNestedMap = nestedMap.Args[0] as NAryExpr;
                        Debug.Assert(nestedNestedMap.Fun is MapSelect);
                        if ((nestedNestedMap.Fun as MapSelect).Arity > 1)
                        {
                            MultiDimensionalMapError();
                        }
                        IndexZ = nestedMap.Args[1];
                        if (!(nestedNestedMap.Args[0] is IdentifierExpr))
                        {
                            Console.WriteLine("*** Error - maps with more than three levels of nesting are not supported");
                            Environment.Exit(1);
                        }
                        ReadVariable = (nestedNestedMap.Args[0] as IdentifierExpr).Decl;
                        this.VisitExpr(nestedNestedMap.Args[1]);
                    }
                    else
                    {
                        Debug.Assert(nestedMap.Args[0] is IdentifierExpr);
                        ReadVariable = (nestedMap.Args[0] as IdentifierExpr).Decl;
                    }
                    this.VisitExpr(nestedMap.Args[1]);

                }
                else
                {
                    Debug.Assert(node.Args[0] is IdentifierExpr);
                    ReadVariable = (node.Args[0] as IdentifierExpr).Decl;
                }
                this.VisitExpr(node.Args[1]);


                if (GlobalVariables.Contains(ReadVariable) || TileStaticVariables.Contains(ReadVariable))
                {
                    accesses.Add(new AccessRecord(ReadVariable, IndexZ, IndexY, IndexX));
                }

                return node;
            }
            else
            {
                return base.VisitNAryExpr(node);
            }
        }



        public override Variable VisitVariable(Variable node)
        {
            if (!(GlobalVariables.Contains(node) || TileStaticVariables.Contains(node)))
            {
                return node;
            }

            accesses.Add(new AccessRecord(node, null, null, null));

            return node;
        }


    }
}
