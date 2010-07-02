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

    private string ExecuteTest(string assemblyName) {

      var host = new Microsoft.Cci.ILToCodeModel.CodeContractAwareHostEnvironment();
      BCT.Host = host;

      IModule/*?*/ module = host.LoadUnitFrom(assemblyName) as IModule;
      if (module == null || module == Dummy.Module || module == Dummy.Assembly) {
        Console.WriteLine(assemblyName + " is not a PE file containing a CLR module or assembly, or an error occurred when loading it.");
        Assert.Fail("Failed to read in test assembly for regression test");
      }

      IAssembly/*?*/ assembly = null;

      PdbReader/*?*/ pdbReader = null;
      string pdbFile = Path.ChangeExtension(module.Location, "pdb");
      if (File.Exists(pdbFile)) {
        Stream pdbStream = File.OpenRead(pdbFile);
        pdbReader = new PdbReader(pdbStream, host);
      }

      module = Decompiler.GetCodeAndContractModelFromMetadataModel(host, module, pdbReader);

      #region Pass 3: Translate the code model to BPL
      var factory = new CLRSemantics();
      MetadataTraverser translator = factory.MakeMetadataTraverser(host.GetContractExtractor(module.ModuleIdentity));
      assembly = module as IAssembly;
      if (assembly != null)
        translator.Visit(assembly);
      else
        translator.Visit(module);
      #endregion Pass 3: Translate the code model to BPL
      Microsoft.Boogie.TokenTextWriter writer = new Microsoft.Boogie.TokenTextWriter(module.Name + ".bpl");
      Prelude.Emit(writer);
      translator.TranslatedProgram.Emit(writer);
      writer.Close();
      var fileName = Path.ChangeExtension(assemblyName, "bpl");
      var s = File.ReadAllText(fileName);
      return s;
    }

    [TestMethod]
    public void TranslationTest() {
      string dir = TestContext.DeploymentDirectory;
      var fullPath = Path.Combine(dir, "RegressionTestInput.dll");
      Stream resource = typeof(UnitTest0).Assembly.GetManifestResourceStream("TranslationTest.RegressionTestInput.txt");
      StreamReader reader = new StreamReader(resource);
      string expected = reader.ReadToEnd();
      var result = ExecuteTest(fullPath);
      if (result != expected) {
        string resultFile = Path.GetFullPath("RegressionTestOutput.txt");
        File.WriteAllText(resultFile, result);
        Assert.Fail("Output didn't match RegressionTestInput.txt: " + resultFile);
      }
    }
  }
}
 