using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;

namespace GPUVerify
{

    class CommandLineOptions
    {

        public static List<string> inputFiles = new List<string>();

        public static string outputFile = null;
        public static string formulaSkeletonsFile = null;
        public static string formulasFile = null;

        public static bool NewRaceDetectionMethod = false;
        public static bool OnlyDivergence = false;
        public static bool FullAbstraction;
        public static bool Inference;
        public static string invariantsFile = null;

        public static int Parse(string[] args)
        {
            for (int i = 0; i < args.Length; i++)
            {
                bool hasColonArgument = false;
                string beforeColon;
                string afterColon = null;
                int colonIndex = args[i].IndexOf(':');
                if (colonIndex >= 0 && (args[i].StartsWith("-") || args[i].StartsWith("/"))) {
                    hasColonArgument = true;
                    beforeColon = args[i].Substring(0, colonIndex);
                    afterColon = args[i].Substring(colonIndex + 1);
                } else {
                    beforeColon = args[i];
                }

                switch (beforeColon)
                {
                    case "-print":
                    case "/print":
                        if (!hasColonArgument)
                        {
                            Console.WriteLine("Error: filename expected after " + beforeColon + " argument");
                            Environment.Exit(1);
                        }
                        Debug.Assert(afterColon != null);
                        outputFile = afterColon;
                    break;

                    case "-generateFormulaSkeletons":
                    case "/generateFormulaSkeletons":
                    if (!hasColonArgument)
                    {
                        Console.WriteLine("Error: filename expected after " + beforeColon + " argument");
                        Environment.Exit(1);
                    }
                    Debug.Assert(afterColon != null);
                    formulaSkeletonsFile = afterColon;
                    break;

                    case "-formulas":
                    case "/formulas":
                    if (!hasColonArgument)
                    {
                        Console.WriteLine("Error: filename expected after " + beforeColon + " argument");
                        Environment.Exit(1);
                    }
                    Debug.Assert(afterColon != null);
                    formulasFile = afterColon;
                    break;

                    case "-newRaceDetectionMethod":
                    case "/newRaceDetectionMethod":
                    NewRaceDetectionMethod = true;

                    break;

                    case "-onlyDivergence":
                    case "/onlyDivergence":
                    OnlyDivergence = true;

                    break;

                    case "-fullAbstraction":
                    case "/fullAbstraction":
                    FullAbstraction = true;

                    break;

                    case "-inference":
                    case "/inference":
                    Inference = true;
                    if (hasColonArgument)
                    {
                        Debug.Assert(afterColon != null);
                        invariantsFile = afterColon;
                    }

                    break;

                    default:
                        inputFiles.Add(args[i]);
                        break;
                }
            }
            return 0;
        }

    }
}
