/*
 ******************************************************************************
 This file is part of BigWoo.NET.

    BigWoo.NET is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    BigWoo.NET is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with BigWoo.NET; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA


    architected and written by 
    matt raffel 
    matt.raffel@mindspring.com

   copyright (c) 2008 by matt raffel unless noted otherwise

 ******************************************************************************
*/
#region using statements
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using BigWoo.NET.ApplicationSupport;
using BigWoo.NET.Utility;
using System.IO;
using BigWoo.Utility;
using CodeCounter.Library; 
#endregion

namespace CodeCounter
{
    /// <summary>
    /// The main control loop for the code counter program.  Evaulates command line arguments
    /// spins up file searches and code counting implmentations to count the code in the file
    /// </summary>
    class Program
    {
        private class PrintHelpException : Exception { }

        private class ShowAboutWebPageException : Exception { }

        #region private data

        private const string COMMAND_VERBOSE = "-verbose";
        private const string COMMAND_RECURSE = "-recurse";
        private const string COMMAND_SUPPORTED = "-supportedTypes";
        private const string COMMAND_SHOWABOUTWEBPAGE = "-about";

        private const string WEBSITE = "www.mattraffel.com/aboutme.aspx";

        private char[] _spinner = new char[] { '|', '/', '-', '\\', '|', '/', '-', '\\' };
        private char[] _osWildCards = new char[] { '*', '?' };
        private object _lockObject = new object();

        private List<string> _fileArgs = new List<string>();
        private ScanResultsList _listOfFiles = new ScanResultsList();
        private ScanForFiles _fileScanner = new ScanForFiles();

        private bool _quiet = true;
        private bool _recursive = false;
        private bool _detailedHelp = false;

        private AutoResetEvent _eventReset = null;
        private int _erasableTextLengh = 0;
        private int _spinnerPosition = 0;
        private string _lastDirectoryProcessed = string.Empty;

        private long _filesCounted = 0L;
        private long _totalLines = 0L;
        private long _codeLines = 0L;
        private long _commentLines = 0L;
        private long _statementLines = 0L;
        private long _errors = 0L;
        #endregion

        #region private methods
        /// <summary>
        /// Draws what might appear to some as a spinner in the console window to 
        /// show that the program is functioning and not hung
        /// </summary>
        private void DrawSpinner()
        {
            // move cursor back to starting position, ignoring if we muck up
            ConsoleBackspace(_erasableTextLengh);

            if (_spinnerPosition >= _spinner.Length)
                _spinnerPosition = 0;

            string outputText = string.Format("{0}", _spinner[_spinnerPosition]);
            Console.Write(outputText);

            _erasableTextLengh = outputText.Length;

            _spinnerPosition++;

        }

        /// <summary>
        /// Erases "spaces" by moving the cursor left by "spaces"
        /// Exceptions are ignored
        /// </summary>
        /// <param name="spaces">int, the number of spaces to backspace</param>
        private void ConsoleBackspace(int spaces)
        {
            try
            {
                if (0 < spaces)
                {
                    int move = spaces;

                    if (spaces > Console.CursorLeft)
                        move = Console.CursorLeft;

                    Console.CursorLeft -= move;
                }
            }
            catch(Exception ex) 
            {
                System.Diagnostics.Debug.WriteLine(ex.Message);
            }
        }

        /// <summary>
        /// processes the command line arguments.  We expect no more than
        ///  -quiet
        ///  -recurse
        ///  -help
        ///  -supportedTypes
        ///  {filename}
        ///  
        /// FileName can be full filename or partial with wild card
        /// </summary>
        /// <param name="args">string[]</param>
        private void ProcessCommandLineArgs(string[] args)
        {
            foreach (string arg in args)
            {
                if (('-' == arg[0]) || (('/' == arg[0])))
                {
                    if (0 == arg.CompareTo(COMMAND_VERBOSE))
                        _quiet = false;
                    else if (0 == arg.CompareTo(COMMAND_RECURSE))
                        _recursive = true;
                    else if (0 == arg.CompareTo(COMMAND_SUPPORTED))
                    {
                        _detailedHelp = true;
                        throw new PrintHelpException();
                    }
                    else if (0 == arg.CompareTo(COMMAND_SHOWABOUTWEBPAGE))
                        throw new ShowAboutWebPageException();
                    else
                        throw new PrintHelpException();
                }
                else
                    _fileArgs.Add(arg);
            }

            if (0 == _fileArgs.Count)
                throw new PrintHelpException();
        }

        /// <summary>
        /// Using a mask, look for files matching the mask, digging recursively
        /// into sub-directories if recursive is true.  While this code can work
        /// for files without a wildcard, for performance reasons the expectation 
        /// is this method is only called when fileMask has a wildcard in it, 
        /// or recursive is true.
        /// </summary>
        /// <param name="fileMask">string</param>
        private void BuildFileListForMask(string fileMask)
        {
            Console.Write(string.Format("scanning for {0}.", fileMask));

            _fileScanner.FilesList = new ScanResultsList();
            _fileScanner.IsRecursive = _recursive;
            _fileScanner.RootDir = Environment.CurrentDirectory;
            _fileScanner.FileMask = fileMask;
            _fileScanner.Scan();

            _listOfFiles.AddRange(_fileScanner.FilesList.ToArray());

            ConsoleBackspace(_erasableTextLengh);
            _erasableTextLengh = 0;

            if (false == _quiet)
                Console.WriteLine("..done");
            else
                Console.WriteLine("");

        }

        /// <summary>
        /// Called when recursive is true, scan for all matches in fileMask
        /// input received from the commandline
        /// </summary>
        private void BuildFileListViaScanner()
        {
            // for each input that "appears" to be a file mask (either a file name or a file wildcard)
            // gather the file names)
            foreach (string fileMask in _fileArgs)
            {
                BuildFileListForMask(fileMask);
            }
        }

        /// <summary>
        /// Called when recursive is false, evaluates the input to see if search is really
        /// required or not, only using the file scanner when a wildcard is present in the
        /// input
        /// </summary>
        private void BuildFileListIntelligently()
        {
            // for each input that "appears" to be a file mask (either a file name or a file wildcard)
            // gather the file names)
            foreach (string fileMask in _fileArgs)
            {
                if (-1 < fileMask.IndexOfAny(_osWildCards))
                {
                    BuildFileListForMask(fileMask);
                }
                else
                {
                    DefaultScanForFilesData nextFile = new DefaultScanForFilesData();
                    nextFile.FileInfo = new FileInfo(fileMask);
                    _listOfFiles.Add(nextFile);
                }
            }
        }

        /// <summary>
        /// optimized building of the file list....if recursive is not true
        /// additional code checks the input and determines how to add files
        /// to the list
        /// </summary>
        private void BuildFileList()
        {
            _listOfFiles.Clear();

            // go ahead and hook up the event handler for file found
            // in case we do end up using the scanner
            _fileScanner.OnFileFound += new FileFoundEvent(OnFileFound);
            _fileScanner.OnDirectoryFound += new ScanningDirectoryEvent(OnDirectoryFound);

            // since recursive is true, it really doesnt matter if 
            // a wild card is in the input, just start scanning
            if (true == _recursive)
            {
                BuildFileListViaScanner();
            }
            else
            {
                BuildFileListIntelligently();
            }
        }

        /// <summary>
        /// File list has been built, now its time to crack open each file
        /// and count the code
        /// </summary>
        private void ProcessFileList()
        {
            // now we are ready to count the files
            CodeCounterEngine codeCounterEngine = new CodeCounterEngine();
            _eventReset = new AutoResetEvent(false);
            object lockObject = new object();

            // hook up finished even handler (required)
            codeCounterEngine.OnFinish += new CodeCounterFinishedEvent(OnCodeCountingFinished);

            if (0 < _listOfFiles.Count)
                Console.WriteLine(string.Format("counting {0} possible files", _listOfFiles.Count));

            // only add these event handlers if the user wanted output
            if (false == _quiet)
            {
                codeCounterEngine.OnStart += new CodeCounterUpdateEvent(OnCodeCountingStart);
                codeCounterEngine.OnUpdate += new CodeCounterUpdateEvent(OnCodeCountingUpdate);
            }

            // for each file in the array
            foreach (IScanForFilesData file in _listOfFiles)
            {
                try
                {
                    codeCounterEngine.File = file.FileInfo;

                    // clean everything up
                    while (true == Console.KeyAvailable)
                        Console.Read();

                    _spinnerPosition = 0;
                    _erasableTextLengh = 0;
                    _eventReset.Reset();

                    // make erasure execute on a separate thread
                    ThreadStart codeCountThreadStart = new ThreadStart(codeCounterEngine.Count);
                    Thread codeCountThread = new Thread(codeCountThreadStart);
                    codeCountThread.Name = "codeCountingThread worker";
                    codeCountThread.Start();

                    _eventReset.WaitOne();
                }
                catch (Exception ex)
                {
                    System.Diagnostics.Debug.WriteLine(ex.Message);
                    Console.WriteLine(ex.Message);
                }
            }
        }

        /// <summary>
        /// Prints help to console
        /// </summary>
        private void PrintHelp()
        {
            Console.WriteLine("");
            Console.WriteLine("\t-verbose");
            Console.WriteLine("\t-recurse");
            Console.WriteLine("\t-supportedTypes");
            Console.WriteLine("\t-help");
            Console.WriteLine("\t-about (opens www.mattraffel.com)");
            Console.WriteLine("\t{filename}");
            Console.WriteLine("");
            Console.WriteLine("FileName can be full filename or partial with wild card");

            // _detailedHelp is set to true when -supportedTypes is found in the command line
            // this means we show information from each of the code counter implmentations
            if (true == _detailedHelp)
            {
                Console.WriteLine("");
                CodeCounterLogicImplementerList list = CodeCounterLogicImplementerList.LoadFromConfigFile();
                if (0 == list.Count)
                {
                    Console.WriteLine("No code types supported.  Check the config file.");
                    return;
                }

                Console.WriteLine("File formats supported:");
                
                foreach (CodeCounterLogicImplementer implementor in list)
                {
                    string[] fileTypeList = implementor.Implementer.FileTypesHandled();
                    foreach (string fileType in fileTypeList)
                    {
                        // most file types are short so we will make a fair assumption
                        // that it is ok to right justify fileType by 10 chars....
                        string details = string.Format("{0,10} by {1}", fileType, implementor.ImplementerType.Name);
                        Console.WriteLine(details);
                    }
                }

            }
        }

        /// <summary>
        /// Prints the results of counting code lines
        /// </summary>
        private void PrintSummaryReport()
        {
            if (false == _quiet)
                Console.WriteLine("");

            Console.WriteLine(string.Format("Files          {0,10:#,##0}", _filesCounted));
            if (0 < _codeLines)
                Console.WriteLine(string.Format("Code Lines     {0,10:#,##0}", _codeLines));

            if (0 < _statementLines)
                Console.WriteLine(string.Format("Statment Lines {0,10:#,##0}", _statementLines));

            Console.WriteLine(string.Format("Comment Lines  {0,10:#,##0}", _commentLines));

            if (0 < _filesCounted)
                Console.WriteLine(string.Format("Avg Lines/File {0,10:#,##0}", _totalLines / _filesCounted));

            if (0 < _errors)
            {
                Console.WriteLine(string.Format("Error Files {0,10:#,##0}", _errors));
                if (true == _quiet)
                    Console.WriteLine(" ==> to see details about the errors run with -verbose");
            }

            Console.WriteLine("");
        }

        /// <summary>
        /// A little extra self boasting.....
        /// </summary>
        private void ShowAboutWebPage()
        {
            try
            {
                Console.WriteLine("");
                Console.WriteLine(string.Format("ok to open {0} in your browser (Y/n)?", WEBSITE));
                ConsoleKeyInfo keyInfo = Console.ReadKey();
                char input = keyInfo.KeyChar;

                if (('y' == input) || ('Y' == input) || ('\r' == input))
                    System.Diagnostics.Process.Start(string.Format("http://{0}", WEBSITE));

                //if ('y' != input)
                //  System.Diagnostics.Process.Start(string.Format("http://{0}", WEBSITE));
            }
            catch
            {
                Console.WriteLine(string.Format("Error trying to open url.  Please visit http://{0} when you have a moment.", WEBSITE));
            }
        }

        /// <summary>
        /// Prints a standard bit of header information every time
        /// </summary>
        private void PrintHeader()
        {
            Console.WriteLine("CodeCounter by matt raffel");
            Console.WriteLine("(c) 2009 - matt.raffel@mindspring.com");
        }

        /// <summary>
        /// This is the main function of this class
        /// it runs through the command line parameters
        /// sets up the FileErasure object and lets it do
        /// its business
        /// </summary>
        /// <param name="args">string[], command line arguments</param>
        private void Run(string[] args)
        {
            PrintHeader();

            try
            {
                // process input
                ProcessCommandLineArgs(args);

                // now we should know what files to count or what mask to use
                // to get the files to count so build a definitive list 
                // of files
                BuildFileList();

                // now count the code
                ProcessFileList();

                // and print out the results
                PrintSummaryReport();
            }
            catch (PrintHelpException)
            {
                PrintHelp();
            }
            catch (ShowAboutWebPageException)
            {
                ShowAboutWebPage();
            }
            catch (Exception error)
            {
                Console.WriteLine("");
                Console.WriteLine("Application Exception:");
                Console.WriteLine(error.Message);
                Console.WriteLine(error.StackTrace);
            }
            finally
            {
            }
        }
        #endregion

        #region event methods
        /// <summary>
        /// Provide simple UI updates on scanning
        /// </summary>
        /// <param name="directoryName">string</param>
        private void OnDirectoryFound(string directoryName)
        {
            if (false == _quiet)
                DrawSpinner();
        }

        /// <summary>
        /// Provide simple UI updates on scanning
        /// </summary>
        /// <param name="fileData">string</param>
        private void OnFileFound(IScanForFilesData fileData)
        {
            if (false == _quiet)
                DrawSpinner();
        }

        /// <summary>
        /// Finished counting lines in a file, now its time to note it
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="counterFinishedArgs">CodeCounterFinishedEventArgs</param>
        private void OnCodeCountingFinished(object sender, CodeCounterFinishedEventArgs counterFinishedArgs)
        {
            lock (_lockObject)
            {
                try
                {

                    if (CodeCounterFunctionTypes.Summarizing == counterFinishedArgs.Function)
                    {
                        if (false == _quiet)
                        {
                            // move cursor back to starting position, ignoring if we muck up
                            ConsoleBackspace(_erasableTextLengh);
                            string spaces = new string(' ', _erasableTextLengh);
                            Console.Write(spaces);
                            Console.WriteLine("");
                        }

                        // only files we succeeding in counting are part of the file count 
                        // error files are not included in the value
                        _filesCounted++;

                        _codeLines += counterFinishedArgs.CodeLines;
                        _totalLines += counterFinishedArgs.Lines;
                        _commentLines += counterFinishedArgs.CommentLines;
                        _statementLines += counterFinishedArgs.StatementLines;

                    }
                    else
                    {
                        _errors++;

                        if ((counterFinishedArgs.AdditionalData is ConfigurationFileException) ||
                            (counterFinishedArgs.AdditionalData is FileTypeNotSupportedException)) 
                        {
                            if (false == _quiet)
                            {
                                // move cursor back to starting position, ignoring if we muck up
                                ConsoleBackspace(_erasableTextLengh);
                                Console.Write("...file type not supported");
                                Console.WriteLine("");
                            }
                        }
                    }

                }
                catch (Exception ex)
                {
                    System.Diagnostics.Debug.WriteLine(ex.Message);
                }
                finally
                {
                    _spinnerPosition = 0;
                    _erasableTextLengh = 0;
                    _eventReset.Set();

                }
            }
        }

        /// <summary>
        /// Updates from the code counter as it evaluates a file
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="erasureArgs">CodeCounterUpdateEventArgs</param>
        private void OnCodeCountingUpdate(object sender, CodeCounterUpdateEventArgs erasureArgs)
        {
            lock (_lockObject)
            {
                try
                {
                    // move cursor back to starting position, ignoring if we muck up
                    DrawSpinner();
                }
                catch (Exception ex)
                {
                    System.Diagnostics.Debug.WriteLine(ex.Message);
                }
            }
        }
        
        /// <summary>
        /// Indicates a file has been found that matches our criteria for counting the lines
        /// of code in the file
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="startArgs">CodeCounterUpdateEventArgs</param>
        private void OnCodeCountingStart(object sender, CodeCounterUpdateEventArgs startArgs)
        {
            try
            {
                System.Diagnostics.Debug.Assert(0 == _erasableTextLengh);

                if (0 != _lastDirectoryProcessed.CompareTo(startArgs.FileInfo.DirectoryName))
                {
                    _lastDirectoryProcessed = startArgs.FileInfo.DirectoryName;
                    string directory = string.Format("{0}:", _lastDirectoryProcessed);
                    Console.WriteLine(directory);
                }

                _spinnerPosition = 0;
                _erasableTextLengh = 0;
                string fileName = string.Format("\t{0}: ", startArgs.FileInfo.Name);
                Console.Write(fileName);
            }
            catch (Exception ex)
            {
                System.Diagnostics.Debug.WriteLine(ex.Message);
            }
        }
        #endregion

        #region ctor
        /// <summary>
        /// 
        /// </summary>
        internal Program()
        {
        }
        #endregion

        #region startup entry method
        /// <summary>
        /// 
        /// </summary>
        /// <param name="args">string[]</param>
        static void Main(string[] args)
        {
            Program go = new Program();
            go.Run(args);

            if (true == System.Diagnostics.Debugger.IsAttached)
            {
                Console.WriteLine("press a key....");
                Console.Read();
            }
        } 
        #endregion
    }
}
