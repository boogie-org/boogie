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

  def main(args: Array[String]): Unit = {
    var boogiePath = "C:\\boogie\\Binaries\\Boogie.exe"
    val inputs = new ListBuffer[String]()
    var printProgram = false
    var doTypecheck = true
    var doTranslate = true
    var boogieArgs = " ";
    var gen = false;
    var showFullStackTrace = false
		
    // closures should be idempotent
    val options = Map(
     "-print" -> {() => printProgram = true},
     "-noTranslate" -> {() => doTranslate = false},
     "-noTypecheck"-> {() => doTypecheck = false},
     "-vs" -> {() => vsMode = true},
     "-checkLeaks" -> {() => checkLeaks = true},
     "-noDeadlockChecks" -> {() => skipDeadlockChecks = true},
     "-noTermination" -> {() => skipTermination = true},
     "-defaults" -> {() => defaults = 3},
     "-gen" -> {() => gen = true},
     "-autoFold" -> {() => autoFold = true},
     "-autoMagic"-> {() => autoMagic = true},
     "-noFreeAssume" -> {() => noFreeAssume = true},
     "-showFullStackTrace" -> {() => showFullStackTrace = true}
    )
    lazy val help = options.keys.foldLeft("syntax: chalice")((s, o) => s + " [" + o + "]") +
    " [-boogie:path]" +
    " [-defaults:int]" +
    " <boogie option>*" +
    " <file.chalice>*";

    for (a <- args) {
     if (options contains a) options(a)()
     else if (a == "-help") {Console.out.println(help); return}
     else if (a.startsWith("-boogie:")) boogiePath = a.substring(8)
     else if (a.startsWith("-defaults:")) {
       try {
         defaults = Integer.parseInt(a.substring(10));
         if (3<=defaults) { autoMagic = true; }
       } catch { case _ => CommandLineError("-defaults takes integer argument", help); }
     }
     else if (a.startsWith("-percentageSupport:")) {
       try {
         val in = Integer.parseInt(a.substring("-percentageSupport:".length));
         if (in < 0 || in > 3) CommandLineError("-percentageSupport takes only values 0,1,2 or 3", help)
         else percentageSupport = in
       } catch { case _ => CommandLineError("-percentageSupport takes integer argument", help); }
     }
     else if (a.startsWith("-") || a.startsWith("/"))
			boogieArgs += ('"' + a + '"' + " ")
				// other arguments starting with "-" or "/" are sent to Boogie.exe
				/* [MHS] Quote whole argument to not confuse Boogie with arguments that
				 * contain spaces, e.g. if Chalice is invoked as
				 *   chalice -z3exe:"C:\Program Files\z3\z3.exe" program.chalice
				 */
     else inputs += a
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
       if (printProgram) PrintProgram.P(prog)
       prog
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
           while(line!=null){
             Console.out.println(line);
             Console.out.flush;
             previous_line = line;
             line = input.readLine();
           }
           boogie.waitFor;
           input.close;

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
}

class InternalErrorException(val msg: String) extends Throwable
class NotSupportedException(val msg: String) extends Throwable
