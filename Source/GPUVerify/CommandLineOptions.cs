using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace GPUVerify
{

    class CommandLineOptions
    {

        public static List<string> inputFiles = new List<string>();

        public static int Parse(string[] args)
        {
            for (int i = 0; i < args.Length; i++)
            {
                inputFiles.Add(args[i]);
            }
            return 0;
        }

    }
}
