using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace GPUVerify
{
    abstract class GPUVerifier : CheckingContext
    {
        protected Program Program;

        protected Procedure KernelProcedure;
        protected Implementation KernelImplementation;
        protected Procedure BarrierProcedure;

        protected List<Variable> ThreadLocalVariables = new List<Variable>();
        protected List<Variable> TileStaticVariables = new List<Variable>();
        protected List<Variable> GlobalVariables = new List<Variable>();

        protected HashSet<string> ReservedNames = new HashSet<string>();

        public GPUVerifier(Program program)
            : base((IErrorSink)null)
        {
            this.Program = program;
        }

        abstract internal void doit();

        virtual internal int Check()
        {
            BarrierProcedure = CheckExactlyOneBarrierProcedure();
            KernelProcedure = CheckExactlyOneKernelProcedure();

            if (ErrorCount > 0)
            {
                return ErrorCount;
            }

            if (BarrierProcedure.InParams.Length != 0)
            {
                Error(BarrierProcedure, "Barrier procedure must not take any arguments");
            }

            if (BarrierProcedure.OutParams.Length != 0)
            {
                Error(BarrierProcedure, "Barrier procedure must not return any results");
            }

            FindGlobalVariables(Program);

            CheckKernelImplementation();

            return ErrorCount;
        }



        private void FindGlobalVariables(Program program)
        {
            foreach (Declaration D in program.TopLevelDeclarations)
            {
                if (D is Variable && (D as Variable).IsMutable)
                {
                    if (!ReservedNames.Contains((D as Variable).Name))
                    {
                        GlobalVariables.Add(D as Variable);
                    }
                }
            }
        }

        protected void CheckWellFormedness()
        {
            int errorCount = Check();
            if (errorCount != 0)
            {
                Console.WriteLine("{0} GPUVerify format errors detected in {1}", errorCount, CommandLineOptions.inputFiles[CommandLineOptions.inputFiles.Count - 1]);
                Environment.Exit(1);
            }
        }

        protected Procedure CheckExactlyOneKernelProcedure()
        {
            return CheckSingleInstanceOfAttributedProcedure(Program, "kernel");
        }

        protected Procedure CheckExactlyOneBarrierProcedure()
        {
            return CheckSingleInstanceOfAttributedProcedure(Program, "barrier");
        }

        private Procedure CheckSingleInstanceOfAttributedProcedure(Program program, string attribute)
        {
            Procedure attributedProcedure = null;

            foreach (Declaration decl in program.TopLevelDeclarations)
            {
                if (!QKeyValue.FindBoolAttribute(decl.Attributes, attribute))
                {
                    continue;
                }

                if (decl is Procedure)
                {
                    if (attributedProcedure == null)
                    {
                        attributedProcedure = decl as Procedure;
                    }
                    else
                    {
                        Error(decl, "\"{0}\" attribute specified for procedure {1}, but it has already been specified for procedure {2}", attribute, (decl as Procedure).Name, attributedProcedure.Name);
                    }

                }
                else
                {
                    Error(decl, "\"{0}\" attribute can only be applied to a procedure", attribute);
                }
            }

            if (attributedProcedure == null)
            {
                Error(program, "\"{0}\" attribute has not been specified for any procedure.  You must mark exactly one procedure with this attribute", attribute);
            }

            return attributedProcedure;
        }

        private void FindLocalVariables()
        {
            foreach (LocalVariable LV in KernelImplementation.LocVars)
            {
                if (!QKeyValue.FindBoolAttribute(LV.Attributes, "tile_static"))
                {
                    ThreadLocalVariables.Add(LV);
                }
            }
        }

        private void FindTileStaticVariables()
        {
            foreach (LocalVariable LV in KernelImplementation.LocVars)
            {
                if (QKeyValue.FindBoolAttribute(LV.Attributes, "tile_static"))
                {
                    TileStaticVariables.Add(LV);
                }
            }
        }

        private void GetKernelImplementation()
        {
            foreach (Declaration decl in Program.TopLevelDeclarations)
            {
                if (!(decl is Implementation))
                {
                    continue;
                }

                Implementation Impl = decl as Implementation;

                if (Impl.Proc == KernelProcedure)
                {
                    KernelImplementation = Impl;
                    break;
                }

            }

            if (KernelImplementation == null)
            {
                Error(Token.NoToken, "*** Error: no implementation of kernel procedure");
            }
        }




        protected virtual void CheckKernelImplementation()
        {
            CheckKernelParameters();
            GetKernelImplementation();

            if (KernelImplementation == null)
            {
                return;
            }

            FindLocalVariables();
            FindTileStaticVariables();
            CheckNoReturns();
        }

        private void CheckNoReturns()
        {
            // TODO!
        }

        protected abstract void CheckKernelParameters();


        internal List<Variable> GetThreadLocalVariables()
        {
            return ThreadLocalVariables;
        }

        internal List<Variable> GetTileStaticVariables()
        {
            return TileStaticVariables;
        }

        internal List<Variable> GetGlobalVariables()
        {
            return GlobalVariables;
        }

    }
}
