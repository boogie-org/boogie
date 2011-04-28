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
using BigWoo.Utility;
#endregion

namespace CodeCounter.Library
{
    /// <summary>
    /// 
    /// </summary>
    public class CodeCounterLogicImplementer
    {
        private string _className = string.Empty;
        private string _fullClassName = string.Empty;
        private string _assemblyName = "CodeCounter.Library.dll";
        private Type _implementer = null;
        private ICodeCounterLogic _logic = null;

        private Type GetImplementerTypeInstance()
        {
            if (null == _implementer)
            {
                if (true == string.IsNullOrEmpty(_assemblyName))
                    throw new ConfigurationFileException("codeCounters not configured correctly");

                if (true == string.IsNullOrEmpty(_fullClassName))
                    throw new ConfigurationFileException("codeCounters not configured correctly");

                _implementer = AssemblyUtility.GetTypeFromFile(_assemblyName, _fullClassName);

                if (false == AssemblyUtility.HasInterface(typeof(ICodeCounterLogic), _implementer))
                    throw new ConfigurationFileException("codeCounters not implemented correctly");
            }

            return _implementer;
        }

        private ICodeCounterLogic GetImplementerInstance()
        {
            if (null == _logic)
            {
                _logic = AssemblyUtility.InvokeDefaultCtor(ImplementerType) as ICodeCounterLogic;
            }

            return _logic;
        }

        public Type ImplementerType
        {
            get { return GetImplementerTypeInstance(); }
        }

        public ICodeCounterLogic Implementer
        {
            get { return GetImplementerInstance(); }
        }

        protected CodeCounterLogicImplementer() { }

        public static CodeCounterLogicImplementer FromConfigElement(CodeCounterLogicElement element)
        {
            CodeCounterLogicImplementer implementer = new CodeCounterLogicImplementer();
            string[] typeParts = element.AssemblyInformation.Split(new char[] { ',' });

            if (null != typeParts)
            {
                if (1 <= typeParts.Length)
                    implementer._className = typeParts[0].Trim();

                if (2 <= typeParts.Length)
                    implementer._fullClassName = typeParts[1].Trim();

                if (3 <= typeParts.Length)
                    implementer._assemblyName = typeParts[2].Trim();
            }
            return implementer;
        }
    }

    /// <summary>
    /// 
    /// </summary>
    public class CodeCounterLogicImplementerList : List<CodeCounterLogicImplementer> 
    {
        protected CodeCounterLogicImplementerList() { }

        public static CodeCounterLogicImplementerList LoadFromConfigFile()
        {
            CodeCounterLogicImplementerList list = new CodeCounterLogicImplementerList();

            CodeCounterTypesConfigurationSection section = ConfigurationManager.GetSection("codeCounters") as CodeCounterTypesConfigurationSection;

            if (null == section)
                throw new ConfigurationFileException("codeCounters section is missing");

            foreach (CodeCounterLogicElement element in section.CounterImplementations)
            {
                CodeCounterLogicImplementer implementer = CodeCounterLogicImplementer.FromConfigElement(element);
                list.Add(implementer);
            }

            return list;
        }
    }
}
