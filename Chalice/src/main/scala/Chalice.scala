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

  def main(args: Array[String]): Unit = {
    var boogiePath = "C:\\boogie\\Binaries\\Boogie.exe"
    val inputs = new ListBuffer[String]()
    var printProgram = false
    var doTypecheck = true
    var doTranslate = true
    var boogieArgs = " ";
    var gen = false;
    var showFullStackTrace = false

    // help texts and closures for boolean command line options
    // closures should be idempotent
    import scala.collection.immutable.ListMap
    val options = ListMap[String,(() => Unit, String)](
     "help" -> (
       {() => },
       "print this message"),
     "print" -> (
       {() => printProgram = true},
       "print intermediate versions of the Chalice program"),
     "noTranslate" -> (
       {() => doTranslate = false},
       "do not translate the program to Boogie (only parse and typecheck)"),
     "noTypecheck"-> (
       {() => doTypecheck = false},
       "do not typecheck the program (only parse). Implies /noTranslate."),
     "vs" -> (
       {() => vsMode = true},
       "Microsoft Visual Studio mode (special error reporting for Visual Studio; requires an existing, writable directory at C:\\tmp)"),
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
       {() => gen = true},
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
       {() => showFullStackTrace = true},
       "show the full stack trace if an exception is encountered"),
     "smoke" -> (
       {() => smoke = true},
       "smoke testing; try to find unreachable code, preconditions/invariants/predicates that are equivalent to false and assumptions that introduce contradictions, by trying to prove 'false' at various positions."),
     "smokeAll" -> (
       {() => smokeAll = true; smoke = true},
       "aggressive smoke testing; try to prove false after every statement.")
    )
    // help text for options with arguments
    val nonBooleanOptions = ListMap(
      "boogie:<file>" -> "use the executable of Boogie at <file>",
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
     if (a == "/help" || a == "-help") {Console.out.println(help); return}
     else if ((a.startsWith("-") || a.startsWith("/")) && (options contains a.substring(1))) options(a.substring(1))._1()
     else if (a.startsWith("/boogie:") || a.startsWith("-boogie:")) boogiePath = a.substring(8)
     else if (a.startsWith("/defaults:") || a.startsWith("-defaults:")) {
       try {
         defaults = Integer.parseInt(a.substring(10));
         if (3<=defaults) { autoMagic = true; }
       } catch { case _ => CommandLineError("-defaults takes integer argument", help); }
     }
     else if (a.startsWith("/percentageSupport:") || a.startsWith("-percentageSupport:")) {
       try {
         val in = Integer.parseInt(a.substring(19));
         if (in < 0 || in > 3) CommandLineError("/percentageSupport takes only values 0,1,2 or 3", help)
         else percentageSupport = in
       } catch { case _ => CommandLineError("/percentageSupport takes integer argument", help); }
     }
     else if (a.startsWith("-boogieOpt:") || a.startsWith("/boogieOpt:"))
            boogieArgs += ("\"/" + a.substring(11) + "\"" + " ")
     else if (a.startsWith("-bo:") || a.startsWith("/bo:"))
            boogieArgs += ("\"/" + a.substring(4) + "\"" + " ")
                /* [MHS] Quote whole argument to not confuse Boogie with arguments that
                 * contain spaces, e.g. if Chalice is invoked as
                 *   chalice -z3exe:"C:\Program Files\z3\z3.exe" program.chalice
                 */
     else if (a.startsWith("-z3opt:") || a.startsWith("/z3opt:"))
            boogieArgs += ("\"/z3opt:" + a.substring(7) + "\"" + " ")
     else if (a.startsWith("-") || a.startsWith("/")) {
       CommandLineError("unkonwn command line parameter: "+a.substring(1), help)
       return
     }
     else inputs += a
    }
    
    // for smoke testing, we want to see all failing assertions, so we use no
    // error limit (or a very high one), and turn the subsumption option off
    if (smoke) {
      boogieArgs += ("\"-errorLimit:10000\" ")
    }
    
    percentageSupport match {
      case 0 => TranslatorPrelude.addComponent(PercentageStandardPL)
      case 1 => TranslatorPrelude.addComponent(PercentageStandardPL, PercentageFixedDenominatorPL)
      case 2 => TranslatorPrelude.addComponent(PercentageFunctionPL)
      case 3 => TranslatorPrelude.addComponent(PercentageUninterpretedFunctionPL)
    }

    // check that input files exist
    var files = for (input <- inputs.toList) yield {
     val file = new File(input);
     if(! file.exists) {
       CommandLineError("input file " + file.getName() + " could not be found", help);
       return
     }
     file;
    }

    // parse programs
    val parser = new Parser();
    val parseResults = if (files.isEmpty) {
      println("No input file provided. Use 'chalice /help' for a list of all available command line options. Reading from stdin...")
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
         Console.err.println("Error: " + e);
       Nil
     case parser.Success(prog, _) =>
       val pprog = if (smoke) SmokeTest.smokeProgram(prog) else prog
       if (printProgram) PrintProgram.P(pprog)
       pprog
    }).flatten;
    if (parseErrors) return;

    // typecheck program
    if (doTypecheck) {
     Resolver.Resolve(program) match {
       case Resolver.Errors(msgs) =>
         if (!vsMode) Console.err.println("The program did not typecheck.");
         msgs foreach { msg => ReportError(msg._1, msg._2) }
       case Resolver.Success() =>
         if (printProgram) {
           Console.out.println("Program after type checking: ");
           PrintProgram.P(program)
         }
         if (doTranslate) {
           // checking if Boogie.exe exists
           val boogieFile = new File(boogiePath);
           if(! boogieFile.exists() || ! boogieFile.isFile()) {
             CommandLineError("Boogie.exe not found at " + boogiePath, help); return
           }
           // translate program to Boogie
           val translator = new Translator();
           var bplProg: List[Boogie.Decl] = Nil
           try {
             bplProg = translator.translateProgram(program);
           } catch {
             case e:InternalErrorException => {
               if (showFullStackTrace) {
                 e.printStackTrace()
                 Console.err.println()
                 Console.err.println()
               }
               CommandLineError("Internal error: " + e.msg, help)
               return
             }
             case e:NotSupportedException => {
               if (showFullStackTrace) {
                 e.printStackTrace()
                 Console.err.println()
                 Console.err.println()
               }
               CommandLineError("Not supported: " + e.msg, help)
               return
             }
           }
           // write to out.bpl
           val bplText = TranslatorPrelude.P + (bplProg map Boogie.Print).foldLeft(""){ (a, b) => a + b };
           val bplFilename = if (vsMode) "c:\\tmp\\out.bpl" else "out.bpl"
           writeFile(bplFilename, bplText);
           // run Boogie.exe on out.bpl
           val boogie = Runtime.getRuntime.exec(boogiePath + " /errorTrace:0 " + boogieArgs + bplFilename);
           // terminate boogie if interrupted
           Runtime.getRuntime.addShutdownHook(new Thread(new Runnable() {
             def run {
               try {
                 val kill = Runtime.getRuntime.exec("taskkill /T /F /IM Boogie.exe");
                 kill.waitFor;
               } catch {case _ => }
               // just to be sure
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
               Console.out.println(line);
               Console.out.flush;
             }
             boogieOutput += line
             previous_line = line;
             line = input.readLine();
           }
           boogie.waitFor;
           input.close;
           
           // smoke test output
           if (smoke) {
             val output = SmokeTest.processBoogieOutput(boogieOutput.toList)
             Console.out.println(output);
             Console.out.flush;
           }

           // generate code
           if(gen && (previous_line != null) && previous_line.endsWith(" 0 errors")) { // hack
             val converter = new ChaliceToCSharp();
             println("Code generated in out.cs.");
             writeFile("out.cs", converter.convertProgram(program));
           }
         }
     }
    }
  }

  def writeFile(filename: String, text: String) {
    val writer = new FileWriter(new File(filename));
    writer.write(text);
    writer.flush();
    writer.close();
  }

  def CommandLineError(msg: String, help: String) = {
    Console.err.println("Error: " + msg)
  }

  def ReportError(pos: Position, msg: String) = {
    if (vsMode) {
     val (r,c) = (pos.line, pos.column)     
     Console.out.println(r + "," + c + "," + r + "," + (c+5) + ":" + msg);
    } else {
     Console.err.println(pos + ": " + msg)
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

