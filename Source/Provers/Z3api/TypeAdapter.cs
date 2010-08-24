using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Diagnostics;
using Microsoft.Contracts;
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
                       (x.IsInt == y.IsInt);
            }

            public int GetHashCode(BasicType basicType)
            {
                if (basicType.IsBool)
                    return 1;
                else if (basicType.IsInt)
                    return 2;
                else
                    throw new Exception("Basic Type " + basicType.ToString() + " is unkwown");
            }
        }

        private Dictionary<MapType, Z3Type> mapTypes = new Dictionary<MapType, Z3Type>(new MapTypeComparator());
        private Dictionary<BvType, Z3Type> bvTypes = new Dictionary<BvType, Z3Type>(new BvTypeComparator());
        private Dictionary<BasicType, Z3Type> basicTypes = new Dictionary<BasicType, Z3Type>(new BasicTypeComparator());
        private Z3Context container;

        public Z3TypeCachedBuilder(Z3Context context)
        {
            this.container = context;
        }

        private Z3Type GetMapType(MapType mapType)
        {
            Context z3 = ((Z3SafeContext)container).z3;
            if (!mapTypes.ContainsKey(mapType))
            {
                Debug.Assert(mapType.Arguments.Length == 1, "Z3api only supports maps of arity 1");
                Z3Type domain = GetType(mapType.Arguments[0]);
                Z3Type range = GetType(mapType.Result);
                Z3Type typeAst = BuildMapType(domain, range);
                mapTypes.Add(mapType, typeAst);
            }
            Z3Type result;
            bool containsKey = mapTypes.TryGetValue(mapType, out result);
            Debug.Assert(containsKey);
            return result;
        }

        private Z3Type GetBvType(BvType bvType)
        {
            if (!bvTypes.ContainsKey(bvType))
            {
                Z3Type typeAst = BuildBvType(bvType);
                bvTypes.Add(bvType, typeAst);
            }
            Z3Type result;
            bool containsKey = bvTypes.TryGetValue(bvType, out result);
            Debug.Assert(containsKey);
            return result;
        }

        private Z3Type GetBasicType(BasicType basicType)
        {
            if (!basicTypes.ContainsKey(basicType))
            {
                Z3Type typeAst = BuildBasicType(basicType);
                basicTypes.Add(basicType, typeAst);
            }
            Z3Type result;
            bool containsKey = basicTypes.TryGetValue(basicType, out result);
            Debug.Assert(containsKey);
            return result;
        }

        public virtual Z3Type GetType(Type boogieType)
        {
            if (boogieType.GetType().Equals(typeof(BvType)))
                return GetBvType((BvType)boogieType);
            else if (boogieType.GetType().Equals(typeof(BasicType)))
                return GetBasicType((BasicType)boogieType);
            else if (boogieType.GetType().Equals(typeof(MapType)))
                return GetMapType((MapType)boogieType);
            else
                throw new Exception("Boogie Type " + boogieType.GetType() + " is unknown");
        }

        private Z3Type WrapType(Sort typeAst)
        {
            return new Z3SafeType(typeAst);
        }

        public Z3Type BuildMapType(Z3Type domain, Z3Type range)
        {
            Context z3 = ((Z3SafeContext)container).z3;
            Sort typeAst = z3.MkArraySort(((Z3SafeType)domain).TypeAst, ((Z3SafeType)range).TypeAst);
            return WrapType(typeAst);
        }

        public Z3Type BuildBvType(BvType bvType)
        {
            Context z3 = ((Z3SafeContext)container).z3;
            Sort typeAst = z3.MkBvSort((uint)bvType.Bits);
            return WrapType(typeAst);
        }

        public Z3Type BuildBasicType(BasicType basicType)
        {
            Context z3 = ((Z3SafeContext)container).z3;
            Sort typeAst;
            if (basicType.IsBool)
            {
                typeAst = z3.MkBoolSort();
            }
            else if (basicType.IsInt)
            {
                typeAst = z3.MkIntSort();
            }
            else
                throw new Exception("Unknown Basic Type " + basicType.ToString());
            return WrapType(typeAst);
        }
    }

    public class Z3Type { }
}