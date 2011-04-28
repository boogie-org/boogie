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
using System.IO;
using System.Security.AccessControl;
using CodeCounter.Library; 
#endregion

namespace CodeCounter
{
    /// <summary>
    /// This is the class that processes a file.  If manages the "conversation" with the
    /// ICodeCounterLogic implementation occuring during reading through the file.
    /// </summary>
    public class CodeCounterEngine
    {
        #region private data
        private FileInfo _fileInfo = null;
        private long _statementLines = 0L;
        private long _totalLines = 0L;
        private long _codeLines = 0L;
        private long _commentLines = 0L;
        private long _errors = 0L;
        private CodeCounterLogicImplementerList _implementerList = null;
        #endregion

        #region properties
        /// <summary>
        /// FileInfo instance of the file we want to count code.
        /// </summary>
        public FileInfo File
        {
            get { return _fileInfo; }
            set { _fileInfo = value; }
        } 
        #endregion

        #region event firing helpers
        /// <summary>
        /// Fires the OnStartEvent if there are listeners.  This 
        /// event is fired once per file.
        /// </summary>
        /// <param name="startArgs">CodeCounterUpdateEventArgs</param>
        private void FireOnStartEvent(CodeCounterUpdateEventArgs startArgs)
        {
            if (null != OnStart)
            {
                OnStart(this, startArgs);
            }
        }

        /// <summary>
        /// Fires OnUpdate event if there are listeners.  This event
        /// is fired approx every 250 lines read in the file.
        /// </summary>
        /// <param name="updateArgs">CodeCounterUpdateEventArgs</param>
        private void FireOnUpdateEvent(CodeCounterUpdateEventArgs updateArgs)
        {
            if (null != OnUpdate)
                OnUpdate(this, updateArgs);
        }

        /// <summary>
        /// Fires OnFinish event if there are listeners.  This event
        /// is fired once per file
        /// </summary>
        /// <param name="finishedArgs">CodeCounterFinishedEventArgs</param>
        private void FireOnFinishedEvent(CodeCounterFinishedEventArgs finishedArgs)
        {
            if (null != OnFinish)
                OnFinish(this, finishedArgs);
        }
        #endregion

        #region private methods
        /// <summary>
        /// Find the ICodeCounterLogic implementation that can work with the file type we 
        /// have found.
        /// </summary>
        /// <exception cref="FileTypeNotSupportedException">Thrown if no logic is found for the given file type</exception>
        /// <exception cref="ConfigurationFileException">Thrown if no logic is defined in the config file</exception>
        /// <returns>ICodeCounterLogic</returns>
        private ICodeCounterLogic GetFileProcessor(FileInfo info)
        {
            if (null == _implementerList)
            {
                _implementerList = CodeCounterLogicImplementerList.LoadFromConfigFile();
                if (0 == _implementerList.Count)
                    throw new ConfigurationFileException("No code counter logic found.");
            }

            ICodeCounterLogic handler = null;

            foreach (CodeCounterLogicImplementer implementer in _implementerList)
            {
                ICodeCounterLogic potentialHandler = implementer.Implementer;

                if (true == potentialHandler.CanProcessFile(info.Name))
                {
                    handler = potentialHandler;
                    break;
                }
            }

            if (null == handler)
                throw FileTypeNotSupportedException.CreateException(info);

            return handler;
        }

        /// <summary>
        /// Each count is file specific.  It is up to the consumer to process
        /// those values
        /// </summary>
        private void InitializeCounters()
        {
            _statementLines = 0L;
            _totalLines = 0L;
            _codeLines = 0L;
            _commentLines = 0L;
            _errors = 0L;
        }
        #endregion

        #region public methods
        /// <summary>
        /// The heart of the counting of lines
        /// </summary>
        public void Count()
        {
            // nothing to process if we have no file name
            if (null == _fileInfo)
                return;

            // ensures member data is reset to default
            InitializeCounters();
            long linesRead = 0L;

            // event arg initialization
            CodeCounterFinishedEventArgs finishedArgs = new CodeCounterFinishedEventArgs(_fileInfo, CodeCounterFunctionTypes.Error);
            CodeCounterUpdateEventArgs startArgs = new CodeCounterUpdateEventArgs(_fileInfo, CodeCounterFunctionTypes.ProcessingFiles);
            CodeCounterUpdateEventArgs updateEventArg = new CodeCounterUpdateEventArgs(_fileInfo, CodeCounterFunctionTypes.ProcessingFiles);

            try
            {
                // let console know we found a file
                FireOnStartEvent(startArgs);

                // find the appropriate handler for the type
                ICodeCounterLogic processor = GetFileProcessor(_fileInfo);
                bool _processorDeterminesEmpty = processor.EngineCanDetermineBlankLines();

                // allow the ICodeCounterLogic implementation a chance to 
                // do something with the file
                processor.PrefileProcessing(_fileInfo.FullName);

                // now we can read through each line and count what it contains
                using (TextReader fileReader = _fileInfo.OpenText())
                {
                    string line = "";

                    while (null != (line = fileReader.ReadLine()))
                    {
                        linesRead++;

                        long mod = (linesRead % 250L);

                        if (0L == mod)
                        {
                            updateEventArg.Lines = linesRead;
                            FireOnUpdateEvent(updateEventArg);
                        }

                        string trimmed = line.Trim();

                        // when the processor does not know or care how empty lines are determined
                        // we will do it by testing for null or empty line.  
                        if ((true == _processorDeterminesEmpty) && (true == string.IsNullOrEmpty(trimmed)))
                            continue;

                        // now we are ready to let the implemention decide what the line is
                        CodeCounterLineType lineType = processor.LineType(trimmed);

                        switch (lineType)
                        {
                            case CodeCounterLineType.Statement:
                            case CodeCounterLineType.Code:
                                _codeLines++;
                                break;
                            case CodeCounterLineType.StatementAndComment:
                            case CodeCounterLineType.CodeAndComment:
                                _codeLines++;
                                _commentLines++;
                                break;
                            case CodeCounterLineType.CommentOnly:
                                _commentLines++;
                                break;
                            default:
                                break;
                        }

                        if (CodeCounterLineType.EmptyLine != lineType)
                            _totalLines++;
                    }

                    // yay we are done
                    fileReader.Close();

                    // allow the counter implemenation any final moments
                    processor.PostfileProcessing(_fileInfo.FullName);

                    finishedArgs.Function = CodeCounterFunctionTypes.Summarizing;
                }                
            }
            catch (Exception ex)
            {
                System.Diagnostics.Debug.WriteLine(ex.Message);
                finishedArgs.Function = CodeCounterFunctionTypes.Error;
                finishedArgs.AdditionalData = ex;
            }
            finally
            {
                finishedArgs.FileInfo = _fileInfo;
                finishedArgs.CodeLines = _codeLines;
                finishedArgs.CommentLines = _commentLines;
                finishedArgs.StatementLines = _statementLines;
                finishedArgs.Lines = _totalLines;
                _fileInfo = null;

                FireOnFinishedEvent(finishedArgs);
            }
        }
        #endregion

        #region event member delcaration
        public event CodeCounterUpdateEvent OnStart;
        public event CodeCounterUpdateEvent OnUpdate;
        public event CodeCounterFinishedEvent OnFinish; 
        #endregion
    }
}
