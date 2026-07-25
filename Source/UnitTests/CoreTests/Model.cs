using System.Globalization;
using System.IO;
using System.Threading;
using Microsoft.Boogie;
using NUnit.Framework;

namespace ModelTests
{
  [TestFixture()]
  public class ModelTests
  {
    [Test]
    public void ParseRealModelElementsUnderNonInvariantLocale()
    {
      // #1133: Z3 emits reals as "0.0", but a CurrentCulture parse rejects
      // that under comma-decimal locales like fr-FR/pt-PT.
      var originalCulture = Thread.CurrentThread.CurrentCulture;
      try
      {
        Thread.CurrentThread.CurrentCulture = new CultureInfo("fr-FR");

        var m = new Model();
        var e = m.ConstructElement("0.0");
        Assert.IsNotNull(e, "ConstructElement should recognize \"0.0\" as a Real under fr-FR");
        Assert.AreEqual(Model.ElementKind.Real, e.Kind);
        Assert.AreEqual("0.0", e.ToString());

        const string model = "*** MODEL\nf -> 0.0\n*** END_MODEL\n";
        Assert.DoesNotThrow(() => Model.ParseModels(new StringReader(model)),
          "Model parsing should succeed under fr-FR");
      }
      finally
      {
        Thread.CurrentThread.CurrentCulture = originalCulture;
      }
    }

    [Test]
    public void ParseRealModelElements()
    {
      var m = new Model();
      var e1 = m.ConstructElement("1e2");
      Assert.AreEqual(e1.Kind, Model.ElementKind.Real);
      Assert.AreEqual(e1.ToString(), "1e2");
      var e2 = m.ConstructElement("-3e5");
      Assert.AreEqual(e2.Kind, Model.ElementKind.Real);
      Assert.AreEqual(e2.ToString(), "-3e5");
      var e3 = m.ConstructElement("1.2e3");
      Assert.AreEqual(e3.Kind, Model.ElementKind.Real);
      Assert.AreEqual(e3.ToString(), "1.2e3");
      var e4 = m.ConstructElement("-3.1e6");
      Assert.AreEqual(e4.Kind, Model.ElementKind.Real);
      Assert.AreEqual(e4.ToString(), "-3.1e6");
    }
    
    [Test]
    public void ParseBoolModelElements()
    {
      var m = new Model();
      var e1 = m.ConstructElement("true");
      Assert.AreEqual(e1, m.True);
      var e2 = m.ConstructElement("false");
      Assert.AreEqual(e2, m.False);
    }
    
    [Test]
    public void ParseIntModelElements()
    {
      var m = new Model();
      var e1 = m.ConstructElement("3289");
      Assert.AreEqual(e1.Kind, Model.ElementKind.Integer);
      Assert.AreEqual(e1.ToString(), "3289");
      var e2 = m.ConstructElement("-12389");
      Assert.AreEqual(e2.Kind, Model.ElementKind.Integer);
      Assert.AreEqual(e2.ToString(), "-12389");
    }
  }
}