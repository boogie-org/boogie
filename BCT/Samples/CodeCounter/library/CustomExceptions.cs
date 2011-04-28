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
using System.Configuration;
using System.IO;
#endregion


namespace CodeCounter.Library
{
    /// <summary>
    /// 
    /// </summary>
    public class ConfigurationFileException : Exception
    {
        public ConfigurationFileException(string msg) : base(msg) { }
    }

    /// <summary>
    /// 
    /// </summary>
    public class FileTypeNotSupportedException : Exception
    {
        public FileTypeNotSupportedException(string msg) : base(msg) { }

        public static FileTypeNotSupportedException CreateException(FileInfo info)
        {
            string msg = string.Format("{0} was not counted as no implemention for type {1} was found", info.Name, info.Extension);
            return new FileTypeNotSupportedException(msg);
        }
    }
}
