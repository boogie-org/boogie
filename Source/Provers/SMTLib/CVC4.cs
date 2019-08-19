using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie.SMTLib
{
    class CVC4
    {
        static string _proverPath;

        static string CodebaseString()
        {
            Contract.Ensures(Contract.Result<string>() != null);
            return Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location));
        }

        public static string ExecutablePath()
        // throws ProverException, System.IO.FileNotFoundException;
        {
            if (_proverPath == null)
                FindExecutable();
            return _proverPath;
        }

        static void FindExecutable()
        // throws ProverException, System.IO.FileNotFoundException;
        {
            Contract.Ensures(_proverPath != null);

            // Command line option 'cvc4exe' always has priority if set 
            if (CommandLineOptions.Clo.CVC4ExecutablePath != null)
            {
                _proverPath = CommandLineOptions.Clo.CVC4ExecutablePath;
                if (!File.Exists(_proverPath))
                {
                    throw new ProverException("Cannot find prover specified with cvc4exe: " + _proverPath);
                }
                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                }
                return;
            }

            var proverExe = "cvc4.exe";

            if (_proverPath == null)
            {
                // Initialize '_proverPath'
                _proverPath = Path.Combine(CodebaseString(), proverExe);
                string firstTry = _proverPath;

                if (File.Exists(firstTry))
                {
                    if (CommandLineOptions.Clo.Trace)
                    {
                        Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                    }
                    return;
                }
                else
                {
                    throw new ProverException("Cannot find executable: " + firstTry);
                }
            }
        }
    }
}
