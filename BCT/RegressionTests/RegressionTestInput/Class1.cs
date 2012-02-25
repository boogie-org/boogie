using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;

namespace RegressionTestInput {

  [AttributeUsage(AttributeTargets.Method)]
  public class AsyncAttribute : Attribute { }

  public class Class0 {

    static int StaticInt;

    static int StaticMethod(int x) {
      return x + 1;
    }

    void M(int x) {
      int y = (5 / x) + (x = 3);
      Contract.Assert(x == 3 && y <= 8);
      StaticInt = y;
      Contract.Assert(y == StaticInt);
    }

    // Test to make sure we generate unique procedure names
    void M(int x, int y) { }
    void M(bool b) { }
    void M(Class0 c) { }

    int NonVoid() {
      return 3 + StaticInt + StaticMethod(3);
    }

    int OutParam(out int x) {
      x = 3 + StaticInt;
      return x;
    }

    int RefParam(ref int x) {
      x = x + 1;
      StaticInt = x;
      return x;
    }

    int AssignToInParam(int x) {
      x = x + 1;
      StaticInt = x;
      return x;
    }

    [AsyncAttribute]
    int MethodThatRepresentsAnAynchronousMethod(int x) {
      return x;
    }

    int CallAsyncMethod(int y) {
      return MethodThatRepresentsAnAynchronousMethod(y);
    }


  }
  class ClassWithBoolTypes {
    static bool staticB;
    bool b;

    static bool M(int x, int y) {
      return x < y;
    }

    public ClassWithBoolTypes(bool z) {
      this.b = z;
      if (z) ClassWithBoolTypes.staticB = z;
    }

    public static void Main() {
      ClassWithBoolTypes.M(3, 4);
    }
  }

  class ClassWithArrayTypes
  {
    public static void Main1()
    {
      int[] s = new int[5];
      s[0] = 2;
      Contract.Assert(s[0] == 2);

      int[] t = new int[4];
      t[0] = 1;
      Contract.Assert(t[0] == 1);

      Contract.Assert(s[0] == 2);
    }

    public static int[] s;
    public static void Main2()
    {
      s = new int[5];
      s[0] = 2;
      Contract.Assert(s[0] == 2);

      int[] t = new int[4];
      t[0] = 1;
      Contract.Assert(t[0] == 1);

      Contract.Assert(s[0] == 2);
    }

    public int[] a;
    public void Main3(int x)
    {
      a[x] = 42;
      a[x + 1] = 43;
      Contract.Assert(a[x + 1] == a[x] + 1);
    }

    public void Main4(int[] xs) {
      if (xs != null && xs.Length > 0) {
        a[0] = xs[0];
      }
    }
  }

  public class WriteToTheHeapAValueReadFromTheHeap {
    int x;
    int y;
    public void M() {
      this.y = this.x;
    }
  }

  public struct S {
    public int x;
    public bool b;
  }

  public class CreateStruct {
    public S Create() {
      var s = new S();
      Contract.Assert(s.x == 0);
      Contract.Assert(s.b == false);
      return s;
    }
    S AssignThreeToSDotX(S s) {
      s.x = 3;
      Contract.Assert(s.x == 3);
      return s;
    }

  }

  public class RefParameters {
    public static void M(ref int x) {
      x++;
    }
  }

  public class RealNumbers {
    public void WriteDouble(double d) {
      Console.WriteLine(d);
    }
    public void ObjectToDouble(object o) {
      WriteDouble((double)o);
    }
    public void RealOperations() {
      double d = 3.0;
      double d2 = 4.0;
      WriteDouble(d + d2);
      WriteDouble(d - d2);
      WriteDouble(d * d2);
      WriteDouble(d / d2);
    }
  }

  public class BitwiseOperations {
    public int BitwiseAnd(int x, int y) { return x & y; }
    public int BitwiseOr(int x, int y) { return x | y; }
    public int ExclusiveOr(int x, int y) { return x ^ y; }
    public int BitwiseNegation(int x) { return ~x; }
  }

  public class NestedGeneric {
    public class C {
      public class G<T> where T : new() {
        public G(int x) {
          var y = new T(); // test to make sure index is calculated correctly for type function
        }
      }
    }
  }
  public class TestForClassesDifferingOnlyInBeingGeneric {
    public int x;
  }

  public class TestForClassesDifferingOnlyInBeingGeneric<T> {
    public int x;
  }

  public struct StructContainingStruct {
    public double d;
    public S s;

    public StructContainingStruct ReturnCopy(StructContainingStruct s) {
      StructContainingStruct t = s;
      return t;
    }

  }

}
