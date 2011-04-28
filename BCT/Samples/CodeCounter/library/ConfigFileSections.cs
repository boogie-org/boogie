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
#endregion

namespace CodeCounter.Library
{
    /// <summary>
    /// 
    /// </summary>
    public class CodeCounterTypesConfigurationSection : ConfigurationSection
    {
        [ConfigurationProperty("counterImplementations")]
        public CodeCounterLogicCollection CounterImplementations
        {
            get { return ((CodeCounterLogicCollection)(base["counterImplementations"])); }
        }
    }

    /// <summary>
    /// 
    /// </summary>
    [ConfigurationCollection(typeof(CodeCounterLogicElement), AddItemName = "logic")]
    public class CodeCounterLogicCollection : ConfigurationElementCollection
    {
        /// <summary>
        /// for creating new elements
        /// </summary>
        /// <returns>AssemblyElement</returns>
        protected override ConfigurationElement CreateNewElement()
        {
            return new CodeCounterLogicElement();
        }

        /// <summary>
        /// searchs the collection for a given AssemblyElement based on its key
        /// </summary>
        /// <param name="element">AssemblyElement</param>
        /// <returns>CodeCounterType</returns>
        protected override object GetElementKey(ConfigurationElement element)
        {
            return (element as CodeCounterLogicElement).AssemblyInformation;
        }

        /// <summary>
        /// Indexor into the array
        /// </summary>
        /// <param name="idx">int</param>
        /// <returns>CodeCounterType</returns>
        public CodeCounterLogicElement this[int idx]
        {
            get
            {
                return BaseGet(idx) as CodeCounterLogicElement;
            }
        }
    }

    /// <summary>
    /// 
    /// </summary>
    public class CodeCounterLogicElement : ConfigurationElement
    {        
        [ConfigurationProperty("assemblyInformation", IsKey = false, IsRequired = true)]
        public string AssemblyInformation
        {
            get
            {
                // assemblyInformation="CSharpCodeCounterLogic, CodeCounter.Library.CSharpCodeCounterLogic, CodeCounter.Library.dll"
                string assemblyInformation = (string) base["assemblyInformation"];
                return assemblyInformation;
            }

            set
            {
                base["assemblyInformation"] = value;
            }
        }

        [ConfigurationProperty("key", IsKey = true, IsRequired = true)]
        public string Key
        {
            get 
            {
                string key = (string) base["key"];
                return key; 
            }
            set { base["key"] = value; }
        }
    }


}
