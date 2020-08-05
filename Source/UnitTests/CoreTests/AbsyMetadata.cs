using Microsoft.Boogie;
using NUnit.Framework;
using System;

namespace CoreTests
{
  [TestFixture()]
  public class AbsyMetadata
  {
    private Absy GetAbsy()
    {
      // The choice of Absy type here is arbitrary
      return new AssertCmd(Token.NoToken, Expr.True);
    }

    [Test()]
    public void NoMetadata()
    {
      var absy = GetAbsy();

      Assert.AreEqual(0, absy.NumberedMetaDataCount);

      Assert.Throws(typeof(ArgumentOutOfRangeException), () => absy.GetMetadata<string>(0));
    }

    [Test()]
    public void InvalidIndex()
    {
      var absy = GetAbsy();

      Assert.AreEqual(0, absy.NumberedMetaDataCount);
      absy.SetMetadata(0, "hello");

      Assert.Throws(typeof(ArgumentOutOfRangeException), () => absy.GetMetadata<string>(1));
    }

    [Test()]
    public void SimpleMetadata()
    {
      var absy = GetAbsy();
      Assert.AreEqual(0, absy.NumberedMetaDataCount);

      var string1 = "hello";
      var string2 = "hello2";
      absy.SetMetadata(0, string1);
      Assert.AreEqual(1, absy.NumberedMetaDataCount);
      absy.SetMetadata(1, string2);
      Assert.AreEqual(2, absy.NumberedMetaDataCount);

      Assert.AreSame(string1, absy.GetMetadata<string>(0));
      Assert.AreSame(string2, absy.GetMetadata<string>(1));

      // Now try iterating over the metadata
      int count = 0;
      foreach (var o in absy.NumberedMetadata)
      {
        Assert.AreEqual(count, o.Key);
        Assert.IsNotNull(o.Value);
        ++count;
      }

      Assert.AreEqual(2, count);
    }

    [Test()]
    public void IncorrectType()
    {
      var absy = GetAbsy();
      Assert.AreEqual(0, absy.NumberedMetaDataCount);

      var string0 = "hello world";
      absy.SetMetadata(0, string0);

      // Now try retrive wrong type
      Assert.Throws(typeof(InvalidCastException), () => absy.GetMetadata<int>(0));
    }

    [Test()]
    public void NullPadding()
    {
      var absy = GetAbsy();
      Assert.AreEqual(0, absy.NumberedMetaDataCount);

      string foo = "foo";
      absy.SetMetadata<string>(10, foo);
      Assert.AreEqual(11, absy.NumberedMetaDataCount);

      // Should nulls be made accessible? Right now its impossible to access
      // them as we always throw an exception if the stored item is null
      for (int i = 0; i <= 9; ++i)
      {
        try
        {
          absy.GetMetadata<String>(i);
          Assert.Fail("Accesing unset metadata should of failed");
        }
        catch (InvalidCastException)
        {
        }
      }


      Assert.AreSame(foo, absy.GetMetadata<String>(10));
    }
  }
}