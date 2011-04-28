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
using System.Text;
using System.IO; 
#endregion

namespace CodeCounter.Library
{
    /// <summary>
    /// Used by ICodeCounterLogic implementations to inform the the code counting engine
    /// the type of line read.
    /// </summary>
    public enum CodeCounterLineType
    {
        /// <summary>
        /// a blank line
        /// </summary>
        EmptyLine,
        /// <summary>
        /// this line contains code only
        /// </summary>
        Code,
        /// <summary>
        /// this line contains code and comments
        /// </summary>
        CodeAndComment,
        /// <summary>
        /// line line is part of a comment and no code
        /// </summary>
        CommentOnly,
        /// <summary>
        /// a complete code statement (like in cs a statement ends with ;)
        /// </summary>
        Statement,
        /// <summary>
        /// this line contains a completed code statement and comments 
        /// </summary>
        StatementAndComment,
    }

    /// <summary>
    /// Interface that defines the methods required by implementtions that provide
    /// the code counting functions
    /// </summary>
    public interface ICodeCounterLogic
    {
        /// <summary>
        /// Evaluates input and determines what the line contains: nothing,
        /// code, code and comments or comment only, statement etc...
        /// </summary>
        /// <param name="line">string, typically one line a source file</param>
        /// <returns>CodeCounterLineType</returns>
        CodeCounterLineType LineType(string line);

        /// <summary>
        /// should return something like cs or vb or sql etc.  No need to return .cs just cs
        /// Typically used to display the supported types during command line help command
        /// </summary>
        /// <returns>string[]</returns>        
        string[] FileTypesHandled();

        /// <summary>
        /// Called by the engine to ask the implementation if it can count the lines in the file
        /// </summary>
        /// <param name="fileName"></param>
        /// <returns>bool, true if the file can be processed</returns>
        bool CanProcessFile(string file);

        /// <summary>
        /// Determines who is responsible for identifying an empty line.  An empty line
        /// being a line that contains no comments and no code.  (Currently unused)
        /// </summary>
        /// <returns>true, the engine will determine what constitues a blank line
        /// other wise the ICodeCounterLogic Implmentation makes that decision</returns>
        bool EngineCanDetermineBlankLines();

        /// <summary>
        /// opportunity to do some processing prior to counting.  If your code
        /// grabs a system handle to this file, make sure you release it before
        /// the function terminates or counting fails.  
        /// </summary>
        /// <param name="fileName">string, full path to the file</param>
        void PrefileProcessing(string fileName);

        /// <summary>
        /// opportunity to do some processing after counting
        /// </summary>
        /// <param name="fileName">string, full path to the file</param>
        void PostfileProcessing(string fileName);

    }
}
