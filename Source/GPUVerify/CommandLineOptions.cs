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

                    default:
                        inputFiles.Add(args[i]);
                        break;
                }
            }
            return 0;
        }

    }
}
