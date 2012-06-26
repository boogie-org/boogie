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
                Console.WriteLine("*** Error: No input files were specified.");
                Environment.Exit(1);
            }

            foreach (string file in CommandLineOptions.inputFiles)
            {
                string extension = Path.GetExtension(file);
                if (extension != null)
                {
                    extension = extension.ToLower();
                }
                if (extension != ".gbpl")
                {
                    Console.WriteLine("Warning '{0}': Should only pass filename with extension .gbpl. Input must be GBoogie programs.", file);
                }
            }

            parseProcessOutput();
        }

        public static Program parse(out ResolutionContext rc)
        {
            Program program = ParseBoogieProgram(CommandLineOptions.inputFiles, false);
            if (program == null)
            {
                Environment.Exit(1);
            }

            Microsoft.Boogie.CommandLineOptions.Clo.DoModSetAnalysis = true;

            rc = new ResolutionContext(null);
            program.Resolve(rc);
            if (rc.ErrorCount != 0)
            {
                Console.WriteLine("{0} name resolution errors detected in {1}", rc.ErrorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                Environment.Exit(1);
            }
            
            int errorCount = program.Typecheck();
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
            ResolutionContext rc;
            Program newProgram = parse(out rc);
            RaceInstrumenter ri = new RaceInstrumenter();
            GPUVerifier newGp = new GPUVerifier(filename, newProgram, rc, ri);
            ri.setVerifier(newGp);

            
            Variable newG = findClonedVar(v, newGp.NonLocalState.getGlobalVariables());
            Variable newT = findClonedVar(v, newGp.NonLocalState.getGroupSharedVariables());
            Contract.Assert(newG == null || newT == null);

            ri.NonLocalStateToCheck.getGlobalVariables().Clear();
            ri.NonLocalStateToCheck.getGroupSharedVariables().Clear();
            ri.onlyLog1 = a1;
            ri.onlyLog2 = a2;

            if (newG != null)
            {
                ri.NonLocalStateToCheck.getGlobalVariables().Add(newG);
            }

            if (newT != null)
            {
                ri.NonLocalStateToCheck.getGroupSharedVariables().Add(newT);
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
            else if (CommandLineOptions.inputFiles.Count == 1)
            {
                var inputFile = CommandLineOptions.inputFiles[0];
                if (Path.GetExtension(inputFile).ToLower() != ".bpl")
                    fn = Path.GetFileNameWithoutExtension(inputFile);
            }
            ResolutionContext rc;
            Program program = parse(out rc);
            IList<GPUVerifier> result = new List<GPUVerifier>();
            GPUVerifier g = new GPUVerifier(fn, program, rc, new NullRaceInstrumenter());

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
                    RaceInstrumenter ri = new RaceInstrumenter();
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
            Microsoft.Boogie.CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());

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
                        Console.WriteLine("{0} parse errors detected in {1}", errorCount, bplFileName);
                        okay = false;
                        continue;
                    }
                }
                catch (IOException e)
                {
                    Console.WriteLine("Error opening file \"{0}\": {1}", bplFileName, e.Message);
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
