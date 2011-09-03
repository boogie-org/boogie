using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    class WriteCollector : AccessCollector
    {

        private AccessRecord access = null;

        public WriteCollector(GPUVerifier verifier)
            : base(verifier)
        {
        }

        public override AssignLhs VisitSimpleAssignLhs(SimpleAssignLhs node)
        {
            Debug.Assert(NoWrittenVariable());
            if (verifier.GetGlobalVariables().Contains(node.DeepAssignedVariable) || verifier.GetTileStaticVariables().Contains(node.DeepAssignedVariable))
            {
                access = new AccessRecord(node.DeepAssignedVariable, new LiteralExpr(node.tok, BigNum.FromInt(0)), new LiteralExpr(node.tok, BigNum.FromInt(0)), new LiteralExpr(node.tok, BigNum.FromInt(0)));
            }
            return node;
        }

        private bool NoWrittenVariable()
        {
            return access == null;
        }

        public override AssignLhs VisitMapAssignLhs(MapAssignLhs node)
        {
            Debug.Assert(NoWrittenVariable());

            if (!(verifier.GetGlobalVariables().Contains(node.DeepAssignedVariable) || verifier.GetTileStaticVariables().Contains(node.DeepAssignedVariable)))
            {
                return node;
            }

            Variable WrittenVariable = node.DeepAssignedVariable;

            MapAssignLhs MapAssignX = node;

            CheckMapIndex(MapAssignX);
            Expr IndexX = MapAssignX.Indexes[0];
            Expr IndexY = new LiteralExpr(Token.NoToken, BigNum.FromInt(0));
            Expr IndexZ = new LiteralExpr(Token.NoToken, BigNum.FromInt(0));

            if (MapAssignX.Map is MapAssignLhs)
            {
                MapAssignLhs MapAssignY = MapAssignX.Map as MapAssignLhs;
                CheckMapIndex(MapAssignY);
                IndexY = MapAssignY.Indexes[0];
                if (MapAssignY.Map is MapAssignLhs)
                {
                    MapAssignLhs MapAssignZ = MapAssignY.Map as MapAssignLhs;
                    CheckMapIndex(MapAssignZ);
                    IndexZ = MapAssignZ.Indexes[0];
                    if (!(MapAssignZ.Map is SimpleAssignLhs))
                    {
                        Console.WriteLine("*** Error - maps with more than three levels of nesting are not supported");
                        Environment.Exit(1);
                    }
                }
                else
                {
                    Debug.Assert(MapAssignY.Map is SimpleAssignLhs);
                }
            }
            else
            {
                Debug.Assert(MapAssignX.Map is SimpleAssignLhs);
            }

            access = new AccessRecord(WrittenVariable, IndexZ, IndexY, IndexX);

            return MapAssignX;
        }

        private void CheckMapIndex(MapAssignLhs node)
        {
            if (node.Indexes.Count > 1)
            {
                MultiDimensionalMapError();
            }
        }




        internal bool FoundWrite()
        {
            return access != null;
        }

        internal AccessRecord GetAccess()
        {
            return access;
        }

    }
}
