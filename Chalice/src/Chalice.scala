//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.File
import java.io.FileWriter
import scala.util.parsing.input.Position

object Chalice {
 def main(args: Array[String]): unit = {
   var boogiePath = "C:\\boogie\\Binaries\\Boogie.exe"
   // parse command-line arguments
   var inputName: String = null
   var printProgram = false
   var vsMode = false;
   def ReportError(pos: Position, msg: String) = {
     if (vsMode) {
       val r = pos.line - 1;
       val c = pos.column - 1;
       Console.out.println(r + "," + c + "," + r + "," + (c+5) + ":" + msg);
     } else {
       Console.err.println(pos + ": " + msg)
     }
   }
   var doTypecheck = true
   var doTranslate = true
   var checkLeaks = false
   // level 0 or below: no defaults
   // level 1: unfold predicates with receiver this in pre and postconditions
   // level 2: unfold predicates and functions with receiver this in pre and postconditions
   // level 3 or above: level 2 + autoMagic
   var defaults = 0
   var autoFold = false
   var autoMagic = false
   var skipDeadlockChecks = false
   var boogieArgs = " ";
   var gen = false;

   for (a <- args) {
     if (a == "-print") printProgram = true
     else if (a == "-noTranslate") doTranslate = false
     else if (a == "-noTypecheck") doTypecheck = false
     else if (a == "-vs") vsMode = true
     else if (a == "-checkLeaks") checkLeaks = true
     else if (a == "-noDeadlockChecks") skipDeadlockChecks = true
     else if (a.startsWith("-boogie:")) boogiePath = a.substring(8)
     else if (a == "-defaults") defaults = 3
     else if (a.startsWith("-defaults:")) { try { defaults = Integer.parseInt(a.substring(10)); if(3<=defaults) { autoMagic = true; } } catch { case _ => CommandLineError("-defaults takes integer argument"); } }
     else if (a == "-gen") { gen = true; }
     else if (a == "-autoFold") autoFold = true
     else if (a == "-autoMagic") autoMagic = true
     else if (a.startsWith("-") || a.startsWith("/")) boogieArgs += (a + " ") // arguments starting with "-" or "/" are sent to Boogie.exe
     else if (inputName != null) { CommandLineError("multiple input filenames: " + inputName + " and " + a); return }
     else { inputName = a }
   }
   // check the command-line arguments
   if (inputName == null && vsMode) {
     inputName = "<stdin>"
   } else if (inputName == null) { CommandLineError("missing input filename"); return } else {
     val file = new File(inputName);
     if(! file.exists()){
       CommandLineError("input file " + file.getName() + " could not be found"); return
     }
   }
   // parse program
   val parser = new Parser();
   parser.parseFile(inputName) match {
     case e: parser.NoSuccess =>
       if (vsMode)
         ReportError(e.next.pos, e.msg);
       else
         Console.err.println("Error: " + e)
     case parser.Success(prog, _) =>
       if (printProgram) PrintProgram.P(prog)
       if (doTypecheck) {
         // typecheck program
         Resolver.Resolve(prog) match {
           case Resolver.Errors(msgs) => 
             if (!vsMode) Console.err.println("The program did not typecheck.");
             msgs foreach { msg => ReportError(msg._1, msg._2) }
           case Resolver.Success() =>
             if (doTranslate) {
               // checking if Boogie.exe exists
               val boogieFile = new File(boogiePath);
               if(! boogieFile.exists() || ! boogieFile.isFile()) {
                 CommandLineError("Boogie.exe not found at " + boogiePath); return
               }
               // translate program to Boogie
               val translator = new Translator();
               // set the translation options
               TranslationOptions.checkLeaks = checkLeaks;
               TranslationOptions.defaults = defaults;
               TranslationOptions.autoFold = autoFold;
               TranslationOptions.autoMagic = autoMagic;
               TranslationOptions.skipDeadlockChecks = skipDeadlockChecks;
               val bplProg = translator.translateProgram(prog);
               // write to out.bpl
               Boogie.vsMode = vsMode;
               val bplText = TranslatorPrelude.P + (bplProg map Boogie.Print).foldLeft(""){ (a, b) => a + b };
               val bplFilename = if (vsMode) "c:\\tmp\\out.bpl" else "out.bpl"
               writeFile(bplFilename, bplText);
               // run Boogie.exe on out.bpl
               val boogie = Runtime.getRuntime().exec(boogiePath + " /errorTrace:0 " + boogieArgs + bplFilename);
               val input = new BufferedReader(new InputStreamReader(boogie.getInputStream()));
               var line = input.readLine();
               var previous_line = null: String;
               while(line!=null){
                 println(line);
                 previous_line = line;
                 line = input.readLine();
               }
               if(gen && (previous_line != null) && previous_line.endsWith(" 0 errors")) { // hack
                 val converter = new ChaliceToCSharp(); 
                 println("Code generated in out.cs.");
                 writeFile("out.cs", converter.convertProgram(prog));
               }
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

 def CommandLineError(msg: String) = {
   Console.err.println("Error: " + msg)
   Console.err.println("syntax: chalice [-print] [-noTypecheck] [-noTranslate] [-vs] [-boogie:path] [-defaults] [-autoFold] [-checkLeaks] [-noDeadlockChecks] inputFile")
 }
}
