using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;

using Microsoft.Boogie;

namespace GPUVerify
{
    class GPUVerify
    {


        public static void Main(string[] args)
        {
            CommandLineOptions.Parse(args);

            if (CommandLineOptions.inputFiles.Count < 1)
            {
                OnlyBoogie.ErrorWriteLine("*** Error: No input files were specified.");
                Environment.Exit(1);
            }

            foreach (string file in CommandLineOptions.inputFiles)
            {
                string extension = Path.GetExtension(file);
                if (extension != null)
                {
                    extension = extension.ToLower();
                }
                if (extension != ".bpl")
                {
                    OnlyBoogie.ErrorWriteLine("*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be BoogiePL programs (.bpl).", file,
                        extension == null ? "" : extension);
                    Environment.Exit(1);
                }
            }

            Program program = ParseBoogieProgram(CommandLineOptions.inputFiles, false);
            if (program == null)
            {
                Environment.Exit(1);
            }

            int errorCount = program.Resolve();
            if (errorCount != 0)
            {
                Console.WriteLine("{0} name resolution errors detected in {1}", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                Environment.Exit(1);
            }

            errorCount = program.Typecheck();

            if (errorCount != 0)
            {
                Console.WriteLine("{0} type checking errors detected in {1}", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                Environment.Exit(1);
            }

            GPUVerifier verifier = new GPUVerifier(program);

            // TODO: check that no non-barrier procedures are called from the kernel

            verifier.AddInitialAndFinalBarriers();

            verifier.SplitBlocksAtBarriers();


            if (CommandLineOptions.formulaSkeletonsFile != null)
            {
                Console.WriteLine("Generating skeleton formulas to \"" + CommandLineOptions.formulaSkeletonsFile + "\" and exiting");
                verifier.GenerateFormulaSkeletons(CommandLineOptions.formulaSkeletonsFile);
                Environment.Exit(0);
            }

            verifier.GenerateBarrierToNextBarriersProcedures();

            verifier.GenerateBarrierToBarrierPairProcedures();

            verifier.GenerateBarrierToNextBarriersVCs();

            verifier.GenerateBarrierToBarrierPairVCs();

            verifier.AddArrayBaseDeclarations();

            using (TokenTextWriter writer = (CommandLineOptions.outputFile == null ? new TokenTextWriter("<console>", Console.Out) : new TokenTextWriter(CommandLineOptions.outputFile)))
            {
                program.Emit(writer);
            }


            /*            errorCount = program.Resolve();
                        if (errorCount != 0)
                        {
                            Console.WriteLine("{0} name resolution errors detected in {1} after transformation", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                            Environment.Exit(1);
                        }

                        errorCount = program.Typecheck();

                        if (errorCount != 0)
                        {
                            Console.WriteLine("{0} type checking errors detected in {1} after transformation", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                            Environment.Exit(1);
                        }
            */
            //Console.ReadLine();

        }







        static Program ParseBoogieProgram(List<string> fileNames, bool suppressTraceOutput)
        {
            Program program = null;
            bool okay = true;
            for (int fileId = 0; fileId < fileNames.Count; fileId++)
            {
                string bplFileName = fileNames[fileId];

                Program programSnippet;
                int errorCount;
                try
                {
                    var defines = new List<string>() { "FILE_" + fileId };
                    errorCount = Parser.Parse(bplFileName, defines, out programSnippet);
                    if (programSnippet == null || errorCount != 0)
                    {
                        OnlyBoogie.ErrorWriteLine("{0} parse errors detected in {1}", errorCount, bplFileName);
                        okay = false;
                        continue;
                    }
                }
                catch (IOException e)
                {
                    OnlyBoogie.ErrorWriteLine("Error opening file \"{0}\": {1}", bplFileName, e.Message);
                    okay = false;
                    continue;
                }
                if (program == null)
                {
                    program = programSnippet;
                }
                else if (programSnippet != null)
                {
                    program.TopLevelDeclarations.AddRange(programSnippet.TopLevelDeclarations);
                }
            }
            if (!okay)
            {
                return null;
            }
            else if (program == null)
            {
                return new Program();
            }
            else
            {
                return program;
            }
        }


    }




}
