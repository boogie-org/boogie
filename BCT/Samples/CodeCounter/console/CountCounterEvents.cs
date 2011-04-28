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
#endregion

namespace CodeCounter
{
    #region CodeCounterFunctionTypes enumeration
    /// <summary>
    /// 
    /// </summary>
    public enum CodeCounterFunctionTypes
    {
        NA,
        ListingFiles,
        ProcessingFiles,
        Summarizing,
        Error
    } 
    #endregion

    #region base Event Arg class
    /// <summary>
    /// 
    /// </summary>
    public class BaseCodeCounterEventArgs : EventArgs
    {
        private FileInfo _fileInfo = null;

        public FileInfo FileInfo
        {
            get { return _fileInfo; }
            set { _fileInfo = value; }
        }

        protected BaseCodeCounterEventArgs() { }

        protected BaseCodeCounterEventArgs(FileInfo fileInfo)
        {
            _fileInfo = fileInfo;
        }
    }
    #endregion

    #region CodeCounterUpdateEventArgs implementation
    /// <summary>
    /// 
    /// </summary>
    public class CodeCounterUpdateEventArgs : BaseCodeCounterEventArgs
    {
        private CodeCounterFunctionTypes _function = CodeCounterFunctionTypes.NA;
        private long _lines = 0;

        public long Lines
        {
            get { return _lines; }
            set { _lines = value; }
        }

        public CodeCounterFunctionTypes Function
        {
            get { return _function; }
            set { _function = value; }
        }

        protected CodeCounterUpdateEventArgs() { }

        public CodeCounterUpdateEventArgs(FileInfo fileInfo, CodeCounterFunctionTypes function)
            : base(fileInfo)
        {
            _function = function;
        }
    } 
    #endregion

    #region CodeCounterFinishedEventArgs declaration
    /// <summary>
    /// 
    /// </summary>
    public class CodeCounterFinishedEventArgs : BaseCodeCounterEventArgs
    {
        private CodeCounterFunctionTypes _function = CodeCounterFunctionTypes.NA;
        private long _totalLines = 0L;
        private long _codeLines = 0L;
        private long _commentLines = 0L;
        private long _statementLines = 0L;
        private object _additionalData = null;

        public object AdditionalData
        {
            get { return _additionalData; }
            set { _additionalData = value; }
        }

        public CodeCounterFunctionTypes Function
        {
            get { return _function; }
            set { _function = value; }
        }

        public long StatementLines
        {
            get { return _statementLines; }
            set { _statementLines = value; }
        }

        public long Lines
        {
            get { return _totalLines; }
            set { _totalLines = value; }
        }

        public long CodeLines
        {
            get { return _codeLines; }
            set { _codeLines = value; }
        }

        public long CommentLines
        {
            get { return _commentLines; }
            set { _commentLines = value; }
        }

        public CodeCounterFinishedEventArgs(FileInfo fileInfo, CodeCounterFunctionTypes function)
            : base(fileInfo)
        {
            _function = function;
        }
        
    } 
    #endregion

    #region event declarations
    public delegate void CodeCounterUpdateEvent(object sender, CodeCounterUpdateEventArgs args);
    public delegate void CodeCounterFinishedEvent(object sender, CodeCounterFinishedEventArgs args); 
    #endregion

}
