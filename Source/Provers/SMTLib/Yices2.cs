//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------


using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie.SMTLib
{
    class Yices2
    {
        static string _proverPath;

        static string CodebaseString()
        {
            Contract.Ensures(Contract.Result<string>() != null);
            return Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location));
        }

        public static string ExecutablePath()
        {
            if (_proverPath == null)
                FindExecutable();
            return _proverPath;
        }

        static void FindExecutable()
        // throws ProverException, System.IO.FileNotFoundException;
        {
            Contract.Ensures(_proverPath != null);

            // Command line option 'yices2exe' always has priority if set 
            if (CommandLineOptions.Clo.Yices2ExecutablePath != null)
            {
                _proverPath = CommandLineOptions.Clo.Yices2ExecutablePath;
                if (!File.Exists(_proverPath))
                {
                    throw new ProverException("Cannot find prover specified with yices2exe: " + _proverPath);
                }
                if (CommandLineOptions.Clo.Trace)
                {
                    Console.WriteLine("[TRACE] Using prover: " + _proverPath);
                }
                return;
            }

            var proverExe = CommandLineOptions.Clo.Yices2ExecutableName; 
            proverExe = proverExe == null ? "yices-smt2.exe" : proverExe;

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

        public static void SetupOptions(SMTLibProverOptions options)
        {
        }
    }
}
