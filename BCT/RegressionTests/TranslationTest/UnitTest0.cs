using System;
using System.Text;
using System.Collections.Generic;
using System.Linq;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.IO;
using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;
using BytecodeTranslator;

namespace TranslationTest {
  /// <summary>
  /// Summary description for UnitTest0
  /// </summary>
  [TestClass]
  public class UnitTest0 {
    public UnitTest0() {
      //
      // TODO: Add constructor logic here
      //
    }

    private TestContext testContextInstance;

    /// <summary>
    ///Gets or sets the test context which provides
    ///information about and functionality for the current test run.
    ///</summary>
    public TestContext TestContext {
      get {
        return testContextInstance;
      }
      set {
        testContextInstance = value;
      }
    }

    #region Additional test attributes
    //
    // You can use the following additional attributes as you write your tests:
    //
    // Use ClassInitialize to run code before running the first test in the class
    // [ClassInitialize()]
    // public static void MyClassInitialize(TestContext testContext) { }
    //
    // Use ClassCleanup to run code after all tests in a class have run
    // [ClassCleanup()]
    // public static void MyClassCleanup() { }
    //
    // Use TestInitialize to run code before running each test 
    // [TestInitialize()]
    // public void MyTestInitialize() { }
    //
    // Use TestCleanup to run code after each test has run
    // [TestCleanup()]
    // public void MyTestCleanup() { }
    //
    #endregion

    private string ExecuteTest(string assemblyName, HeapFactory heapFactory) {
      var options = new Options();
      options.monotonicHeap = true;
      options.dereference = Options.Dereference.Assume;
      BCT.TranslateAssemblyAndWriteOutput(new List<string> { assemblyName }, heapFactory, options, null, false);
      var fileName = Path.ChangeExtension(assemblyName, "bpl");
      var s = File.ReadAllText(fileName);
      return s;
    }

    [TestMethod]
    public void SplitFieldsHeap() {
      string dir = TestContext.DeploymentDirectory;
      var fullPath = Path.Combine(dir, "RegressionTestInput.dll");
      Stream resource = typeof(UnitTest0).Assembly.GetManifestResourceStream("TranslationTest.SplitFieldsHeapInput.txt");
      StreamReader reader = new StreamReader(resource);
      string expected = reader.ReadToEnd();
      var result = ExecuteTest(fullPath, new SplitFieldsHeap());
      if (result != expected) {
        string resultFile = Path.GetFullPath("SplitFieldsHeapOutput.txt");
        File.WriteAllText(resultFile, result);
        var msg = String.Format("Output didn't match: SplitFieldsHeapInput.txt \"{0}\"", resultFile);
        Assert.Fail(msg);
      }
    }

    [TestMethod]
    public void GeneralHeap() {
      string dir = TestContext.DeploymentDirectory;
      var fullPath = Path.Combine(dir, "RegressionTestInput.dll");
      Stream resource = typeof(UnitTest0).Assembly.GetManifestResourceStream("TranslationTest.GeneralHeapInput.txt");
      StreamReader reader = new StreamReader(resource);
      string expected = reader.ReadToEnd();
      var result = ExecuteTest(fullPath, new GeneralHeap());
      if (result != expected) {
        string resultFile = Path.GetFullPath("GeneralHeapOutput.txt");
        File.WriteAllText(resultFile, result);
        var msg = String.Format("Output didn't match: GeneralHeapInput.txt \"{0}\"", resultFile);
        Assert.Fail(msg);
      }
    }

  }
}
 