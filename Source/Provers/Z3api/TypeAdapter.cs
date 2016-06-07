using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Diagnostics;
using Microsoft.Boogie.AbstractInterpretation;
using Microsoft.Boogie;
using Microsoft.Boogie.Z3;
using Microsoft.Z3;
using Microsoft.Boogie.VCExprAST;

namespace Microsoft.Boogie.Z3
{
    internal class Z3TypeCachedBuilder
    {
        private class MapTypeComparator : IEqualityComparer<MapType>
        {
            public bool Equals(MapType x, MapType y)
            {
                if (x.MapArity != y.MapArity)
                    return false;
                for (int i = 0; i < x.MapArity; i++)
                {
                    if (!Equals(x.Arguments[i], y.Arguments[i]))
                        return false;
                }
                return Equals(x.Result, y.Result);

            }
            public int GetHashCode(MapType mapType)
            {
                return mapType.GetHashCode();
            }
        }

        private class BvTypeComparator : IEqualityComparer<BvType>
        {
            public bool Equals(BvType x, BvType y)
            {
                return x.Bits == y.Bits;
            }
            public int GetHashCode(BvType bvType)
            {
                return bvType.Bits;
            }
        }

        private class BasicTypeComparator : IEqualityComparer<BasicType>
        {
            public bool Equals(BasicType x, BasicType y)
            {
                return (x.IsBool == y.IsBool) &&
                       (x.IsInt == y.IsInt) &&
                       (x.IsReal == y.IsReal);
            }

            public int GetHashCode(BasicType basicType)
            {
                if (basicType.IsBool)
                    return 1;
                else if (basicType.IsInt)
                    return 2;
                else if (basicType.IsReal)
                  return 3;
                else
                    throw new Exception("Basic Type " + basicType.ToString() + " is unkwown");
            }
        }

        private class CtorTypeComparator : IEqualityComparer<CtorType> {
          public bool Equals(CtorType x, CtorType y) {
            return (x.Decl.Name == y.Decl.Name);
          }

          public int GetHashCode(CtorType ctorType) {
            return ctorType.Decl.Name.GetHashCode();
          }
        }

        private Dictionary<MapType, Sort> mapTypes = new Dictionary<MapType, Sort>(new MapTypeComparator());
        private Dictionary<BvType, Sort> bvTypes = new Dictionary<BvType, Sort>(new BvTypeComparator());
        private Dictionary<BasicType, Sort> basicTypes = new Dictionary<BasicType, Sort>(new BasicTypeComparator());
        private Dictionary<CtorType, Sort> ctorTypes = new Dictionary<CtorType, Sort>(new CtorTypeComparator());

        private Z3apiProverContext container;

        public Z3TypeCachedBuilder(Z3apiProverContext context)
        {
            this.container = context;
        }

        private Sort GetMapType(MapType mapType) {
          Context z3 = ((Z3apiProverContext)container).z3;
          if (!mapTypes.ContainsKey(mapType)) {
            Type result = mapType.Result;
            for (int i = mapType.Arguments.Length-1; i > 0; i--) {
              GetType(result);
              result = new MapType(mapType.tok, new TypeVariableSeq(), new TypeSeq(mapType.Arguments[i]), result);
            }
            mapTypes.Add(mapType, BuildMapType(GetType(mapType.Arguments[0]), GetType(result)));
          }
          return mapTypes[mapType];
        }

        private Sort GetBvType(BvType bvType)
        {
            if (!bvTypes.ContainsKey(bvType))
            {
                Sort typeAst = BuildBvType(bvType);
                bvTypes.Add(bvType, typeAst);
            }
            Sort result;
            bool containsKey = bvTypes.TryGetValue(bvType, out result);
            Debug.Assert(containsKey);
            return result;
        }

        private Sort GetBasicType(BasicType basicType)
        {
            if (!basicTypes.ContainsKey(basicType))
            {
                Sort typeAst = BuildBasicType(basicType);
                basicTypes.Add(basicType, typeAst);
            }
            Sort result;
            bool containsKey = basicTypes.TryGetValue(basicType, out result);
            Debug.Assert(containsKey);
            return result;
        }

        private Sort GetCtorType(CtorType ctorType) {
          if (!ctorTypes.ContainsKey(ctorType)) {
            Sort typeAst = BuildCtorType(ctorType);
            ctorTypes.Add(ctorType, typeAst);
          }
          Sort result;
          bool containsKey = ctorTypes.TryGetValue(ctorType, out result);
          Debug.Assert(containsKey);
          return result;
        }

        public virtual Sort GetType(Type boogieType) {
          System.Type type = boogieType.GetType();
          if (type.Equals(typeof(BvType)))
            return GetBvType((BvType)boogieType);
          else if (type.Equals(typeof(BasicType)))
            return GetBasicType((BasicType)boogieType);
          else if (type.Equals(typeof(MapType)))
            return GetMapType((MapType)boogieType);
          else if (type.Equals(typeof(CtorType)))
            return GetCtorType((CtorType)boogieType);
          else
            throw new Exception("Boogie Type " + boogieType.GetType() + " is unknown");
        }

        public Sort BuildMapType(Sort domain, Sort range)
        {
            Context z3 = ((Z3apiProverContext)container).z3;
            return z3.MkArraySort(domain, range);
        }

        public Sort BuildBvType(BvType bvType)
        {
            Context z3 = ((Z3apiProverContext)container).z3;
            return z3.MkBvSort((uint)bvType.Bits);
        }

        public Sort BuildBasicType(BasicType basicType)
        {
            Context z3 = ((Z3apiProverContext)container).z3;
            Sort typeAst;
            if (basicType.IsBool)
            {
                typeAst = z3.MkBoolSort();
            }
            else if (basicType.IsInt)
            {
                typeAst = z3.MkIntSort();
            }
            else if (basicType.IsReal)
            {
                typeAst = z3.MkRealSort();
            }
            else
                throw new Exception("Unknown Basic Type " + basicType.ToString());
            return typeAst;
        }

        public Sort BuildCtorType(CtorType ctorType) {
          Context z3 = ((Z3apiProverContext)container).z3;
          if (ctorType.Arguments.Length > 0)
            throw new Exception("Type constructor of non-zero arity are not handled");
          return z3.MkSort(ctorType.Decl.Name);
        }
    }
}