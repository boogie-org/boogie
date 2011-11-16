using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Windows.Forms;



using Microsoft.Boogie;
using System.Diagnostics.Contracts;

namespace GPUVerify
{
    class GPUVerify
    {

        public static void Main(string[] args)
        {
            int showHelp = CommandLineOptions.Parse(args);

            if (showHelp == -1)
            {
                CommandLineOptions.Usage();
                System.Environment.Exit(0);
            }

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

            parseProcessOutput();
        }

        public static Program parse()
        {
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

            return program;
        }

        private static Variable findClonedVar(Variable v1, ICollection<Variable> vars)
        {
            foreach (Variable v2 in vars)
            {
                if (v1.Name.Equals(v2.Name))
                {
                    return v2;
                }
            }
            return null;
        }

        public static bool doit(string filename, Variable v, int a1, int a2)
        {
            Program newProgram = parse();
            RaceInstrumenterBase ri = CommandLineOptions.SetEncoding ? (RaceInstrumenterBase)new SetEncodingRaceInstrumenter() : (RaceInstrumenterBase) new ElementEncodingRaceInstrumenter();
            GPUVerifier newGp = new GPUVerifier(filename, newProgram, ri);
            ri.setVerifier(newGp);

            
            Variable newG = findClonedVar(v, newGp.NonLocalState.getGlobalVariables());
            Variable newT = findClonedVar(v, newGp.NonLocalState.getTileStaticVariables());
            Contract.Assert(newG == null || newT == null);

            ri.NonLocalStateToCheck.getGlobalVariables().Clear();
            ri.NonLocalStateToCheck.getTileStaticVariables().Clear();
            ri.onlyLog1 = a1;
            ri.onlyLog2 = a2;

            if (newG != null)
            {
                ri.NonLocalStateToCheck.getGlobalVariables().Add(newG);
            }

            if (newT != null)
            {
                ri.NonLocalStateToCheck.getTileStaticVariables().Add(newT);
            }
            
            newGp.doit();

            return !ri.failedToFindSecondAccess;

        }

        public static IList<GPUVerifier> parseProcessOutput()
        {
            string fn = "temp";
            if (CommandLineOptions.outputFile != null)
            {
                fn = CommandLineOptions.outputFile;
            }
            Program program = parse();
            IList<GPUVerifier> result = new List<GPUVerifier>();
            GPUVerifier g = new GPUVerifier(fn, program, new NullRaceInstrumenter());

            if (CommandLineOptions.DividedArray)
            {
                bool FoundArray = CommandLineOptions.ArrayToCheck == null;

                foreach (Variable v in g.NonLocalState.getAllNonLocalVariables())
                {
                    if (CommandLineOptions.DividedAccesses)
                    {
                        int i = 0;
                        int j = 0;
                        while (true)
                        {
                            bool res = doit(fn + "." + v.Name + "." + i + "." + (i + j), v, i, j);
                            if (!res)
                            {
                                if (j == 0)
                                {
                                    break;
                                }
                                else
                                {
                                    i++;
                                    j = 0;
                                }
                            }
                            else
                            {
                                j++;
                            }
                        }
                    }
                    else
                    {
                        if (CommandLineOptions.ArrayToCheck == null || CommandLineOptions.ArrayToCheck.Equals(v.Name))
                        {
                            FoundArray = true;
                            doit("temp_" + v.Name, v, -1, -1);
                        }
                    }
                }

                if (!FoundArray)
                {
                    Console.WriteLine("Did not find a non-local array named " + CommandLineOptions.ArrayToCheck);
                    Environment.Exit(1);
                }

            }
            else
            {
                if (!CommandLineOptions.OnlyDivergence)
                {
                    RaceInstrumenterBase ri = CommandLineOptions.SetEncoding ? (RaceInstrumenterBase)new SetEncodingRaceInstrumenter() : (RaceInstrumenterBase)new ElementEncodingRaceInstrumenter();
                    ri.setVerifier(g);
                    g.setRaceInstrumenter(ri);
                }

                g.doit();
                result.Add(g);

            }

            return result;
            
        }





        public static Program ParseBoogieProgram(List<string> fileNames, bool suppressTraceOutput)
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
