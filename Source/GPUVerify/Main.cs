using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Windows.Forms;



using Microsoft.Boogie;

namespace GPUVerify
{
    class GPUVerify
    {
        static bool ASYNCHRONOUS_METHOD = false;

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

            if (ASYNCHRONOUS_METHOD)
            {

                string[] preprocessArguments = new string[CommandLineOptions.inputFiles.Count + 4];
                preprocessArguments[0] = "/noVerify";
                preprocessArguments[1] = "/printUnstructured";
                preprocessArguments[2] = "/print:temp_unstructured.bpl";
                preprocessArguments[3] = Path.GetDirectoryName(Application.ExecutablePath) + "\\..\\..\\BoogieLibrary\\GPUVerifyLibrary.bpl";
                for (int i = 0; i < CommandLineOptions.inputFiles.Count; i++)
                {
                    preprocessArguments[i + 4] = CommandLineOptions.inputFiles[i];
                }

                OnlyBoogie.Main(preprocessArguments);

                if ((CommandLineOptions.formulasFile == null && CommandLineOptions.formulaSkeletonsFile == null) || (CommandLineOptions.formulasFile != null && CommandLineOptions.formulaSkeletonsFile != null))
                {
                    Console.WriteLine("Error, specify one of /formulas:... or /generateFormulaSkeletons:...");
                    Environment.Exit(1);
                }

                CommandLineOptions.inputFiles = new List<string>();
                CommandLineOptions.inputFiles.Add("temp_unstructured.bpl");
                if (CommandLineOptions.formulasFile != null)
                {
                    CommandLineOptions.inputFiles.Add(CommandLineOptions.formulasFile);
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

            verifier.doit();


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
