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

        private Z3TypeBuilder builder;
        private Dictionary<BvType, Z3Type> bvTypes = new Dictionary<BvType, Z3Type>(new BvTypeComparator());
        private Dictionary<BasicType, Z3Type> basicTypes = new Dictionary<BasicType, Z3Type>(new BasicTypeComparator());

        public Z3TypeCachedBuilder(Z3TypeBuilder builder)
        {
            this.builder = builder;
        }

        private Z3Type GetBvType(BvType bvType)
        {
            if (bvTypes.ContainsKey(bvType))
            {
                Z3Type typeAst = builder.BuildBvType(bvType);
                bvTypes.Add(bvType, typeAst);
            }
            Z3Type result;
            bool containsKey = bvTypes.TryGetValue(bvType, out result);
            Debug.Assert(containsKey);
            return result;
        }

        private Z3Type GetBasicType(BasicType basicType)
        {
            if (basicTypes.ContainsKey(basicType))
            {
                Z3Type typeAst = builder.BuildBasicType(basicType);
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
            else
                throw new Exception("Boogie Type " + boogieType.GetType() + " is unknown");
        }
    }

    public class Z3Type { }

    interface Z3TypeBuilder
    {
        Z3Type BuildBvType(BvType bvType);
        Z3Type BuildBasicType(BasicType basicType);
    }


    internal class Z3TransformerTypeCache : Z3TypeCachedBuilder
    {

        private BoogieTypeTransformer transformer;

        public Z3TransformerTypeCache(Z3TypeBuilder builder, BoogieTypeTransformer transformer)
            : base(builder)
        {
            this.transformer = transformer;
        }

        public override Z3Type GetType(Type boogieType)
        {
            Type resolvedBoogieType = transformer.TransformType(boogieType);
            return base.GetType(resolvedBoogieType);
        }
    }

    internal abstract class BoogieTypeTransformer
    {

        protected abstract Type TransformBvType(BvType boogieType);
        protected abstract Type TransformBasicType(BasicType boogieType);

        public Type TransformType(Type boogieType)
        {
            return Dispatch(boogieType);
        }

        private Type Dispatch(Type boogieType)
        {
            if (boogieType.GetType().Equals(typeof(BvType)))
                return TransformBvType((BvType)boogieType);
            else if (boogieType.GetType().Equals(typeof(BasicType)))
                return TransformBasicType((BasicType)boogieType);
            else
                throw new Exception("Boogie Type " + boogieType.GetType() + " is unknown");
        }

    }

    internal class IntTransformer : BoogieTypeTransformer
    {

        protected override Type TransformBvType(BvType bvType)
        {
            // registerBvType(bvType.Bits)
            return BasicType.Int;
        }

        protected override Type TransformBasicType(BasicType boogieType)
        {
            if (boogieType.IsBool)
            {
                // registerBool()
            }
            return BasicType.Int;
        }
    }
}