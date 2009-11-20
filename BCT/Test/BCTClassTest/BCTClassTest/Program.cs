using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace BCTClassTest
{
    abstract class BCTClassTest
    {
        public BCTClassTest()
        {
        }

        public abstract void AbstractMethod();

        public virtual int VirturalMethod(int j)
        {
            return j;
        }

        protected void ProtectedMethod(int j)
        {
            int i = j;
            i++;
        }
    }

    internal class InheritTest : BCTClassTest
    {
        public InheritTest() { }

        public override void AbstractMethod()
        {
            throw new NotImplementedException();
        }

        public override int VirturalMethod(int j)
        {
            ProtectedMethod(j);
            return base.VirturalMethod(j);
        }
    }


    class Program
    {
        static void Main(string[] args)
        {
        }
    }
}
