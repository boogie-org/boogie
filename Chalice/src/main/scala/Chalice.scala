//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
package chalice;
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition
import collection.mutable.ListBuffer

object Chalice {
  /**
   * Reporting options
   */
  private[chalice] var vsMode = false;
  private[chalice] var rise4funMode = false;
  private[chalice] var InputFilename = "";  // the name of the last input file mentioned on the command line, or "" if none

  /**
   * Translation options
   */
  // level 0 or below: no defaults
  // level 1: unfold predicates with receiver this in pre and postconditions
  // level 2: unfold predicates and functions with receiver this in pre and postconditions
  // level 3 or above: level 2 + autoMagic\
  private[chalice] var defaults = 0: Int;
  private[chalice] var autoFold = false: Boolean;
  private[chalice] var checkLeaks = false: Boolean;
  private[chalice] var autoMagic = false: Boolean;
  private[chalice] var skipDeadlockChecks = false: Boolean;
  private[chalice] var skipTermination = false: Boolean;
  private[chalice] var noFreeAssume = false: Boolean;
  // percentageSupport 0: use multiplication directly
  // percentageSupport 1: fix Permission$denominator as constant (possibly unsound for small values of the constant?)
  // percentageSupport 2: use function and provide some (redundant) axioms
  // percentageSupport 3: use an uninterpreted function and axiomatize the properties of multiplication
  private[chalice] var percentageSupport = 2;
  private[chalice] var smoke = false;
  private[chalice] var smokeAll = false;
  private[chalice] var timingVerbosity = 1;

  /**
   * Holds all command line arguments not stored in fields of Chalice.
   * Can only be created parseCommandLine.
   */
  sealed abstract class CommandLineParameters {
    val boogiePath: String 
    val files: List[File]
    val printProgram: Boolean 
    val doTypecheck: Boolean 
    val doTranslate: Boolean 
    val boogieArgs: String 
    val gen: Boolean
    val showFullStackTrace: Boolean
    val noBplFile: Boolean
    val bplFile: String
    def getHelp(): String
  }
  
  def parseCommandLine(args: Array[String]): Option[CommandLineParameters] = {
    // help texts and closures for boolean command line options
    // closures should be idempotent
    import scala.collection.immutable.ListMap
    
    var aBoogiePath = "C:\\boogie\\Binaries\\Boogie.exe"
    val inputs = new ListBuffer[String]()
    var aPrintProgram = false
    var aDoTypecheck = true
    var aDoTranslate = true
    var aNoBplFile = true
    var aBplFile = "out.bpl"
    var aBoogieArgs = " "
    var aGen = false;
    var aShowFullStackTrace = false
    
    val options = ListMap[String,(() => Unit, String)](
     "help" -> (
       {() => },
       "print this message"),
     "print" -> ({() => aNoBplFile = false},"output the Boogie program used for verification to 'out.bpl'"),
     "printIntermediate" -> ({() => aPrintProgram = true},"print intermediate versions of the Chalice program"),
     "noTranslate" -> (
       {() => aDoTranslate = false},
       "do not translate the program to Boogie (only parse and typecheck)"),
     "noTypecheck"-> (
       {() => aDoTypecheck = false},
       "do not typecheck the program (only parse). Implies /noTranslate."),
     "vs" -> (
       {() => vsMode = true},
       "Microsoft Visual Studio mode (special error reporting for Visual Studio; requires an existing, writable directory at C:\\tmp)"),
     "rise4fun" -> (
       {() => rise4funMode = true},
       "rise4fun mode (generates error messages in a format expected by the rise4fun harness"),
     "checkLeaks" -> (
       {() => checkLeaks = true},
       "(no description available)"),
     "noDeadlockChecks" -> (
       {() => skipDeadlockChecks = true},
       "skip all lock ordering checks"),
     "noTermination" -> (
       {() => skipTermination = true},
       "skip the termination checks for functions"),
     "defaults" -> (
       {() => defaults = 3},
       null),
     "gen" -> (
       {() => aGen = true},
       "generate C# code from the Chalice program"),
     "autoFold" -> (
       {() => autoFold = true},
       "automatically fold predicates whenever necessary"),
     "autoMagic" -> (
       {() => autoMagic = true},
       "automatically try to infer accessibility predicates and non-nullness checks in specifications"),
     "noFreeAssume" -> (
       {() => noFreeAssume = true},
       "(no description available)"),
     "showFullStackTrace" -> (
       {() => aShowFullStackTrace = true},
       "show the full stack trace if an exception is encountered"),
     "smoke" -> (
       {() => smoke = true},
       "smoke testing; try to find unreachable code, preconditions/invariants/predicates that are equivalent to false and assumptions that introduce contradictions, by trying to prove 'false' at various positions."),
     "smokeAll" -> (
       {() => smokeAll = true; smoke = true},
       "aggressive smoke testing; try to prove false after every statement."),
     "time" -> (
       {() => timingVerbosity = 2},
       "sets /time:2")
    )
    // help text for options with arguments
    val nonBooleanOptions = ListMap(
      "boogie:<file>" -> "use the executable of Boogie at <file>",
      "print:<file>" -> "print the Boogie program used for verification into file <file>",
      "time:<n>" -> ("output timing information\n"+
          "0: no information is included\n"+
          "1: the overall verification time is output (default)\n"+
          "2: detailed timings for each phase of the verification are output\n"+
          "3: (used for testing only) output the overall verification time on stderr"),
      "defaults:<level>" -> ("defaults to reduce specification overhead\n"+
          "level 0 or below: no defaults\n"+
          "level 1: unfold predicates with receiver this in pre and postconditions\n"+
          "level 2: unfold predicates and functions with receiver this in pre and postconditions\n"+
          "level 3 or above: level 2 + autoMagic"),
      "percentageSupport:<n>" -> ("determin how percentage permissions are translated to Boogie\n"+
          "0: use multiplication directly (can cause performance problems)\n"+
          "1: fix Permission$denominator as constant (possibly unsound)\n"+
          "2: use a function and provide some (redundant) axioms\n"+
          "3: use an uninterpreted function and axiomatize the properties of multiplication"),
      "boogieOpt:<arg>, /bo:<arg>" -> "specify additional Boogie options"
    )
    lazy val help = {
      val maxLength = math.min((nonBooleanOptions.keys++options.keys).map(s => s.length+1).max,14)
      val printOptionHelp = (param: String, help: String) => "\n  /" + param + (" "*(maxLength-param.length-1)) +
                             ": " + help.split("\n").map(h => " "*(maxLength+2+2)+wordWrap(h, 80-2-2-math.max(maxLength,param.length+1)," "*(maxLength+2+2))).mkString("\n").substring(maxLength+2+2)

      "Chalice concurrent program verifier.\nUsage: chalice [option] <filename>+\n"+
      "  where <option> is one of"+
      options.foldLeft("")((acc, v) => acc + (if (v._2._2 == null) "" else printOptionHelp(v._1, v._2._2)))+
      nonBooleanOptions.foldLeft("")((acc, v) => acc + printOptionHelp(v._1, v._2))
    }
    
    for (a <- args) {
     if (a == "/help" || a == "-help") {Console.out.println(help); return None}
     else if ((a.startsWith("-") || a.startsWith("/")) && (options contains a.substring(1))) options(a.substring(1))._1()
     else if (a.startsWith("/print:") || a.startsWith("-print:")) {aBplFile = a.substring(7); aNoBplFile = false}
     else if (a.startsWith("/boogie:") || a.startsWith("-boogie:")) aBoogiePath = a.substring(8)
     else if (a.startsWith("/defaults:") || a.startsWith("-defaults:")) {
       try {
         defaults = Integer.parseInt(a.substring(10));
         if (3<=defaults) { autoMagic = true; }
       } catch { case _ => CommandLineError("-defaults takes integer argument", help); }
     }
     else if (a.startsWith("/percentageSupport:") || a.startsWith("-percentageSupport:")) {
       try {
         val in = Integer.parseInt(a.substring(19));
         if (in < 0 || in > 3) CommandLineError("/percentageSupport takes only values 0, 1, 2 or 3", help)
         else percentageSupport = in
       } catch { case _ => CommandLineError("/percentageSupport takes integer argument", help); }
     }
     else if (a.startsWith("/time:") || a.startsWith("-time:")) {
       try {
         val in = Integer.parseInt(a.substring(6));
         if (in < 0 || in > 3) CommandLineError("/time takes only values 0, 1, 2 or 3", help)
         else timingVerbosity = in
       } catch { case _ => CommandLineError("/time takes integer argument", help); }
     }
     else if (a.startsWith("-boogieOpt:") || a.startsWith("/boogieOpt:"))
            aBoogieArgs += ("\"/" + a.substring(11) + "\"" + " ")
     else if (a.startsWith("-bo:") || a.startsWith("/bo:"))
            aBoogieArgs += ("\"/" + a.substring(4) + "\"" + " ")
                /* [MHS] Quote whole argument to not confuse Boogie with arguments that
                 * contain spaces, e.g. if Chalice is invoked as
                 *   chalice -z3exe:"C:\Program Files\z3\z3.exe" program.chalice
                 */
     else if (a.startsWith("-z3opt:") || a.startsWith("/z3opt:"))
            aBoogieArgs += ("\"/z3opt:" + a.substring(7) + "\"" + " ")
     else if (a.startsWith("-") || a.startsWith("/")) {
       CommandLineError("unknown command line parameter: "+a.substring(1), help)
       return None
     }
     else inputs += a
    }
    
    // for smoke testing, we want to see all failing assertions, so we use no
    // error limit (or a very high one), and turn the subsumption option off
    if (smoke) {
      aBoogieArgs += ("\"-errorLimit:10000\" ")
    }
    
    percentageSupport match {
      case 0 => TranslatorPrelude.addComponent(PercentageStandardPL)
      case 1 => TranslatorPrelude.addComponent(PercentageStandardPL, PercentageFixedDenominatorPL)
      case 2 => TranslatorPrelude.addComponent(PercentageFunctionPL)
      case 3 => TranslatorPrelude.addComponent(PercentageUninterpretedFunctionPL)
    }

    // check that input files exist
    var aFiles = for (input <- inputs.toList) yield {
     val file = new File(input);
     if(! file.exists) {
       CommandLineError("input file " + file.getName() + " could not be found", help);
       return None;
     }
     InputFilename = input
     file;
    }
    
    Some(new CommandLineParameters{
        val boogiePath = aBoogiePath 
        val files = aFiles 
        val printProgram = aPrintProgram 
        val doTypecheck = aDoTypecheck 
        val doTranslate = aDoTranslate 
        val boogieArgs = aBoogieArgs 
        val gen = aGen 
        val showFullStackTrace = aShowFullStackTrace
        val noBplFile = aNoBplFile
        val bplFile = aBplFile
        def getHelp(): String = help
    })
  }
  
  def parsePrograms(params: CommandLineParameters): Option[List[TopLevelDecl]] = {
    val files = params.files;
    val printProgram = params.printProgram;
    
    // parse programs
    val parser = new Parser();
    val parseResults = if (files.isEmpty) {
      if (!vsMode) println("No input file provided. Use 'chalice /help' for a list of all available command line options. Reading from stdin...")
      List(parser.parseStdin)
    } else for (file <- files) yield {
      parser.parseFile(file)
    }

    // report errors and merge declarations
    assert(parseResults.size > 0)
    var parseErrors = false;
    val program:List[TopLevelDecl] = parseResults.map(result => result match {
     case e:parser.NoSuccess =>
       parseErrors = true;
       if (vsMode)
         ReportError(e.next.pos, e.msg);
       else
         Console.out.println("Error: " + e);
       Nil
     case parser.Success(prog, _) =>
       val pprog = if (smoke) SmokeTest.smokeProgram(prog) else prog
       if (printProgram) PrintProgram.P(pprog)
       pprog
    }).flatten;
    if (parseErrors) 
        None
      else
        Some(program)
  }
  
  def typecheckProgram(params: CommandLineParameters, program: List[TopLevelDecl]): Boolean = {
    // typecheck program
    Resolver.Resolve(program) match {
     case Resolver.Errors(msgs) =>
       if (!vsMode) Console.out.println("The program did not typecheck.");
       msgs foreach { msg => ReportError(msg._1, msg._2) };
       false;
     case Resolver.Success() =>
       true
    }
  }

  object VerificationSteps extends Enumeration {
    type VerificationSteps = Value
    val Init = Value("Init")
    val Parse = Value("Parse")
    val TypeCheck = Value("TypeCheck")
    val PrintProgram = Value("PrintProgram")
    val Translate = Value("Translate")
    val Boogie = Value("Boogie")
    val GenerateCode = Value("GenerateCode")
  }

  def main(args: Array[String]): Unit = {

    var timings = scala.collection.immutable.ListMap[VerificationSteps.Value, Long]()
    for (step <- VerificationSteps.values) timings += (step -> 0)
    var startTime = System.nanoTime
    var tmpTime = startTime

    //Parse command line arguments
    val params = parseCommandLine(args) match {
      case Some(p) => p
      case None => return //invalid arguments, help has been displayed
    }

    timings += (VerificationSteps.Init -> (System.nanoTime - tmpTime))
    tmpTime = System.nanoTime

    try {

      val program = parsePrograms(params) match {
        case Some(p) => p
        case None => return //illegal program, errors have already been displayed
      }

      timings += (VerificationSteps.Parse -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
      
      if(!params.doTypecheck || !typecheckProgram(params, program))
        return ;

      timings += (VerificationSteps.TypeCheck -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime

      if (params.printProgram) {
        Console.out.println("Program after type checking: ");
        PrintProgram.P(program)
      }

      timings += (VerificationSteps.PrintProgram -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
      
      if(!params.doTranslate)
        return;
      
      // checking if Boogie.exe exists (on non-Linux machine)
      val boogieFile = new File(params.boogiePath);
      if(! boogieFile.exists() || ! boogieFile.isFile()
              && (System.getProperty("os.name") != "Linux")) {
        CommandLineError("Boogie.exe not found at " + params.boogiePath, params.getHelp()); 
        return;
      }
      
      val boogiePath = params.boogiePath
      val boogieArgs = params.boogieArgs
      
      // translate program to Boogie
      val translator = new Translator();
      var bplProg: List[Boogie.Decl] = Nil
      bplProg = translator.translateProgram(program);

      timings += (VerificationSteps.Translate -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
      
      // write to out.bpl
      val ss = """
function IsGoodExhaleState(eh: HeapType, h: HeapType,
                           m: MaskType, sm: MaskType) returns (bool)
{
  (forall<T> o: ref, f: Field T :: { eh[o, f] }  CanRead(m, sm, o, f) ==> eh[o, f] == h[o, f]) &&
  (forall o: ref :: { eh[o, held] }  (0<eh[o, held]) == (0<h[o, held])) &&
  (forall o: ref :: { eh[o, rdheld] }  eh[o, rdheld] == h[o, rdheld]) &&
  (forall o: ref :: { h[o, held] }  (0<h[o, held]) ==> eh[o, mu] == h[o, mu]) &&
  (forall o: ref :: { h[o, rdheld] }  h[o, rdheld] ==> eh[o, mu] == h[o, mu]) &&
  (forall o: ref :: { h[o, forkK] } { eh[o, forkK] } h[o, forkK] == eh[o, forkK]) &&
  (forall o: ref :: { h[o, held] } { eh[o, held] } h[o, held] == eh[o, held]) &&
  (forall o: ref, f: Field int :: { eh[o, f], PredicateField(f) } PredicateField(f) ==> h[o, f] <= eh[o, f]) &&
  (forall o: ref, f: Field int :: { h[o, predicateMaskField(f)], PredicateField(f) } { eh[o, predicateMaskField(f)], PredicateField(f) } { m[o, predicateMaskField(f)], PredicateField(f) } """
    val ss2 =  (TranslatorPrelude.preds map (x => "{ #"+x.FullName+"#trigger(o), PredicateField(f) }")).mkString(" ")
    val ss3 = """ PredicateField(f) && CanRead(m, sm, o, f) ==>
      (forall<T> o2: ref, f2: Field T :: { h[o2, f2] } { eh[o2, f2] } { m[o2, f2] }  h[o, predicateMaskField(f)][o2, f2] ==> eh[o2, f2] == h[o2, f2])) &&
  (forall o: ref, f: Field int :: { PredicateField(f), eh[o, predicateMaskField(f)] } PredicateField(f) && CanRead(m, sm, o, f) ==> eh[o, predicateMaskField(f)] == h[o, predicateMaskField(f)])
}
      """
      val bplText = TranslatorPrelude.P + ss + ss2 + ss3 + (bplProg map Boogie.Print).foldLeft(""){ (a, b) => a + b };
      val bplFilename = if (vsMode) "c:\\tmp\\out.bpl" else (if (params.noBplFile) "stdin.bpl" else params.bplFile)
      if (!params.noBplFile) writeFile(bplFilename, bplText);
      // run Boogie.exe on out.bpl
      val boogie = Runtime.getRuntime.exec(boogiePath + " /errorTrace:0 " + boogieArgs + "stdin.bpl");
      val output = boogie.getOutputStream()
      output.write(bplText.getBytes)
      output.close
      // terminate boogie if interrupted
      Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
        def run {
          boogie.destroy
        }
      }))
      // the process blocks until we exhaust input and error streams
      new Thread(new Runnable() {
        def run {
          val err = new BufferedReader(new InputStreamReader(boogie.getErrorStream));
          var line = err.readLine;
          while(line!=null) {Console.err.println(line); Console.err.flush}
        }
      }).start;
      val input = new BufferedReader(new InputStreamReader(boogie.getInputStream));
      var line = input.readLine();
      var previous_line = null: String;
      val boogieOutput: ListBuffer[String] = new ListBuffer()
      while (line!=null){
        if (!smoke) {
          if (previous_line != null) Console.out.println
          Console.out.print(line);
          Console.out.flush;
        }
        boogieOutput += line
        previous_line = line;
        line = input.readLine();
      }
      boogie.waitFor;
      input.close;

      timings += (VerificationSteps.Boogie -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
      
      // smoke test output
      if (smoke) {
        val output = SmokeTest.processBoogieOutput(boogieOutput.toList)
        Console.out.print(output);
        Console.out.flush;
      }
      
      // generate code
      if(params.gen && (previous_line != null) && previous_line.endsWith(" 0 errors")) { // hack
        generateCSharpCode(params, program)
      }

      timings += (VerificationSteps.GenerateCode -> (System.nanoTime - tmpTime))
      tmpTime = System.nanoTime
    } catch {
      case e:InternalErrorException => {
        if (params.showFullStackTrace) {
          e.printStackTrace()
          Console.err.println()
          Console.err.println()
        }
        CommandLineError("Internal error: " + e.msg, params.getHelp())
        return
      }
      case e:NotSupportedException => {
        if (params.showFullStackTrace) {
          e.printStackTrace()
          Console.err.println()
          Console.err.println()
        }
        CommandLineError("Not supported: " + e.msg, params.getHelp())
        return
      }
    }

    val time = System.nanoTime - startTime
    if (timingVerbosity == 1) {
      Console.out.println(" in " + ("%1.3f" format (time / 1000000000.0)) + " seconds")
    } else if (timingVerbosity == 2) {
      Console.out.println; Console.out.println
      Console.out.println("Timings Information")
      val max = (timings.keySet.toList.map(a => a.toString.length).sortWith( (a, b) => a > b )).head
      for ((step, time) <- timings) {
        Console.out.println("  " + step + ": " + (" "*(max - step.toString.length)) + ("%1.3f" format (time / 1000000000.0)) + " seconds")
      }
    } else {
      Console.out.println
    }
    if (timingVerbosity == 3) {
      Console.err.println(("%1.3f" format (time / 1000000000.0)))
    }
  }
  
  def generateCSharpCode(params: CommandLineParameters, program: List[TopLevelDecl]): Unit = {    
      val converter = new ChaliceToCSharp();
      println("Code generated in out.cs.");
      writeFile("out.cs", converter.convertProgram(program));
  }

  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text);
    writer.flush();
    writer.close();
  }

  def CommandLineError(msg: String, help: String) = {
    Console.out.println("Error: " + msg)
  }

  def ReportError(pos: Position, msg: String) = {
    if (vsMode) {
     val (r,c) = (pos.line, pos.column)     
     Console.out.println(r + "," + c + "," + r + "," + (c+5) + ":" + msg);
    } else {
     Console.out.println(pos + ": " + msg)
    }
  }
  
  def wordWrap(s: String, l: Int, indent: String): String = {
    var prefix = s.takeWhile(c => c == ' ').length
    if (prefix == 0) prefix = if (s.indexOf(": ") > 0) s.indexOf(": ")+2 else 0;
    val words = s.split(" ")
    var c = 0
    var result = ""
    var first = 0
    for (word <- words) {
      c += word.length + 1
      if (c-1 > l-first*prefix) { result += "\n"; c = word.length + 1; first = 1}
      result += word + " "
    }
    result.substring(0, result.length-1).replace("\n", "\n" + (" "*prefix) + indent).replace(" \n","\n")
  }
}

class InternalErrorException(val msg: String) extends Throwable
class NotSupportedException(val msg: String) extends Throwable

