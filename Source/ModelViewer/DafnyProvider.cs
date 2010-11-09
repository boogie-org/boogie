using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Diagnostics.Contracts;

namespace Microsoft.Boogie.ModelViewer.Dafny
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return m.TryGetFunc("$$Language$Dafny") != null;
    }

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var dm = new DafnyModel(m);
      foreach (var s in m.States) {
        var sn = new StateNode(dm.states.Count, dm, s);
        dm.states.Add(sn);
      }
      return dm;
    }
  }

  class DafnyModel : LanguageModel
  {
    public readonly Model model;
    public readonly Model.Func f_heap_select, f_set_select, f_seq_length, f_seq_index, f_box, f_dim, f_index_field, f_multi_index_field;
    public readonly Dictionary<Model.Element, Model.Element[]> ArrayLengths = new Dictionary<Model.Element, Model.Element[]>();
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();

    public DafnyModel(Model m)
    {
      model = m;
      f_heap_select = m.MkFunc("[3]", 3);
      f_set_select = m.MkFunc("[2]", 2);
      f_seq_length = m.MkFunc("Seq#Length", 1);
      f_seq_index = m.MkFunc("Seq#Index", 2);
      f_box = m.MkFunc("$Box", 1);
      f_dim = m.MkFunc("FDim", 1);
      f_index_field = m.MkFunc("IndexField", 1);
      f_multi_index_field = m.MkFunc("MultiIndexField", 2);

      // collect the array dimensions from the various array.Length functions
      foreach (var fn in m.Functions) {
        if (Regex.IsMatch(fn.Name, "^array[0-9]*.Length[0-9]*$")) {
          int j = fn.Name.IndexOf('.', 5);
          int dims = j == 5 ? 1 : int.Parse(fn.Name.Substring(5, j - 5));
          int idx = j == 5 ? 0 : int.Parse(fn.Name.Substring(j + 7));
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Args[0];
            var len = tpl.Result;
            Model.Element[] ar;
            if (!ArrayLengths.TryGetValue(elt, out ar)) {
              ar = new Model.Element[dims];
              ArrayLengths.Add(elt, ar);
            }
            Contract.Assert(ar[idx] == null);
            ar[idx] = len;
          }
        }
      }
    }

    public override IEnumerable<IState> States
    {
      get { return states; }
    }

    public string GetUserVariableName(string name)
    {
      if (name == "$Heap" || name == "$_Frame" || name == "#cev_pc")
        return null;
      var hash = name.IndexOf('#');
      if (0 < hash)
        return name.Substring(0, hash);
      return name;
    }

    public Model.Element Image(Model.Element elt, Model.Func f)
    {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt)
    {
      List<ElementNode> result = new List<ElementNode>();

      if (elt.Kind == Model.ElementKind.Uninterpreted) {
        var seqLen = f_seq_length.AppWithArg(0, elt);
        if (seqLen != null) {
          // elt is a sequence
          var edgname = new EdgeName(this, "|.|", elt);
          result.Add(new FieldNode(state, edgname, seqLen.Result));
          foreach (var tpl in f_seq_index.AppsWithArg(0, elt)) {
            edgname = new EdgeName(this, "[%0]", tpl.Args[1]);
            result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
          }

        } else {
          // it seems elt is an object or array
          Model.Element[] lengths;
          if (ArrayLengths.TryGetValue(elt, out lengths)) {
            int i = 0;
            foreach (var len in lengths) {
              var name = lengths.Length == 1 ? "Length" : "Length" + i;
              var edgname = new EdgeName(this, name);
              result.Add(new FieldNode(state, edgname, len));
              i++;
            }
          }
          var heap = state.state.TryGet("$Heap");
          if (heap != null) {
            foreach (var tpl in f_heap_select.AppsWithArgs(0, heap, 1, elt)) {
              var field = new FieldName(tpl.Args[2], this);
              var edgname = new EdgeName(this, field.Name, elt);
              result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
            }
          }
        }
      }

      return result;
    }

    class FieldName
    {
      public readonly Model.Element Field;
      public readonly int Dims;
      public readonly int[] dims;  // null if Dims==0
      public readonly string Name;

      public FieldName(Model.Element elt, DafnyModel dm) {
        Field = elt;
        var tpl = dm.f_dim.AppWithArg(0, elt);
        if (tpl != null) {
          Dims = tpl.Result.AsInt();
          if (Dims != 0) {
            dims = new int[Dims];
            for (int i = Dims; 0 <= --i; ) {
              if (i == 0) {
                tpl = dm.f_index_field.AppWithResult(elt);
                dims[i] = tpl.Args[0].AsInt();
              } else {
                tpl = dm.f_multi_index_field.AppWithResult(elt);
                dims[i] = tpl.Args[1].AsInt();
                elt = tpl.Args[0];
              }
            }
          }
        }
        // now for the name
        if (Dims == 0) {
          Name = Field.ToString();
          foreach (var n in Field.Names) {
            Name = n.Func.Name;
            int dot = Name.LastIndexOf('.');
            if (0 <= dot)
              Name = Name.Substring(dot + 1);
            break;
          }
        } else {
          Name = "[";
          string sep = "";
          foreach (var idx in dims) {
            Name += sep + idx;
            sep = ",";
          }
          Name += "]";
        }
      }
    }

    Model.Element Unbox(Model.Element elt) {
      var unboxed = f_box.AppWithResult(elt);
      if (unboxed != null)
        return unboxed.Args[0];
      else
        return elt;
    }
  }

  class StateNode : IState
  {
    internal readonly Model.CapturedState state;
    readonly string name;
    internal readonly DafnyModel dm;
    internal readonly List<VariableNode> vars = new List<VariableNode>();
    internal readonly int index;
    
    public StateNode(int i, DafnyModel parent, Model.CapturedState s)
    {
      dm = parent;
      state = s;
      index = i;

      name = s.Name;
      var idx = name.LastIndexOfAny(new char[] { '\\', '/' });
      if (0 <= idx)
        name = name.Substring(idx + 1);
      var limit = 16;
      if (name.Length > limit) {
        idx = name.IndexOf('(');
        if (idx > 0) {
          var prefLen = limit - (name.Length - idx);
          if (prefLen > 2) {
            name = name.Substring(0,prefLen) + ".." + name.Substring(idx);
          }
        }
      }

      SetupVars();
    }

    void SetupVars()
    {
      var names = Util.Empty<string>();

      if (dm.states.Count > 0) {
        var prev = dm.states.Last();
        names = prev.vars.Map(v => v.realName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names) {
        if (dm.GetUserVariableName(v) != null) {
          var val = state.TryGet(v);
          var vn = new VariableNode(this, v, val);
          vn.updatedHere = dm.states.Count > 0 && curVars.ContainsKey(v);
          if (curVars.ContainsKey(v))
            dm.RegisterLocalValue(vn.Name, val);
          vars.Add(vn);
        }
      }

      dm.Flush(vars);
    }

    public string Name
    {
      get { return name; }
    }

    public IEnumerable<IDisplayNode> Nodes
    {
      get {
        return vars; 
      }
    }

  }

  class ElementNode : DisplayNode
  {
    protected StateNode stateNode;
    protected Model.Element elt;
    protected DafnyModel vm { get { return stateNode.dm; } }

    public ElementNode(StateNode st, EdgeName name, Model.Element elt)
      : base(st.dm, name, elt)
    {
      this.stateNode = st;
      this.elt = elt;
    }

    public ElementNode(StateNode st, string name, Model.Element elt)
      : this(st, new EdgeName(name), elt) { }

    protected override void ComputeChildren()
    {
      children.AddRange(vm.GetExpansion(stateNode, elt));
    }
  }

  class FieldNode : ElementNode
  {
    public FieldNode(StateNode par, EdgeName realName, Model.Element elt)
      : base(par, realName, elt)
    {
      /*
      var idx = realName.LastIndexOf('.');
      if (idx > 0)
        name = realName.Substring(idx + 1);
       */
    }
  }

  class MapletNode : ElementNode
  {
    public MapletNode(StateNode par, EdgeName realName, Model.Element elt)
      : base(par, realName, elt)
    {
    }
  }

  class VariableNode : ElementNode
  {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt)
      : base(par, realName, elt)
    {
      this.realName = realName;
      name = new EdgeName(vm.GetUserVariableName(realName));
    }

    public override NodeState State
    {
      get
      {
        return base.State | (updatedHere ? NodeState.Changed : NodeState.Normal);
      }
    }
  }
}
