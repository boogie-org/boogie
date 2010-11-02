using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

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

    public IEnumerable<IState> GetStates(Model m)
    {
      var dm = new DafnyModel(m);
      foreach (var s in m.States) {
        var sn = new StateNode(dm.states.Count, dm, s);
        dm.states.Add(sn);
      }
      foreach (var s in dm.states) s.ComputeNames();
      Namer.ComputeCanonicalNames(dm.states.Select(s => s.namer));
      Namer.ComputeCanonicalNames(dm.states.Select(s => s.namer));
      // Namer.ComputeCanonicalNames(vm.states.Select(s => s.namer));
      return dm.states;
    }
  }

  class DafnyModel
  {
    public readonly Model model;
    public readonly Model.Func f_heap_select, f_set_select, f_seq_length, f_seq_index, f_box;
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
          var edgname = new EdgeName(state.namer, "|%0|", "|.|", elt);
          result.Add(new FieldNode(state, edgname, seqLen.Result));
          foreach (var tpl in f_seq_index.AppsWithArg(0, elt)) {
            var fieldName = string.Format("[{0}]", tpl.Args[1].ToString());
            edgname = new EdgeName(state.namer, "%0" + fieldName, fieldName, elt);
            result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
          }
        } else {

          var heap = state.state.TryGet("$Heap");
          if (heap != null) {
            foreach (var tpl in f_heap_select.AppsWithArgs(0, heap, 1, elt)) {
              var field = tpl.Args[2];
              var fieldName = field.ToString();
              foreach (var n in field.Names) {
                fieldName = n.Func.Name;
                int dot = fieldName.LastIndexOf('.');
                if (0 <= dot) {
                  fieldName = fieldName.Substring(dot + 1);
                }
                break;
              }
              var val = tpl.Result;
              var edgname = new EdgeName(state.namer, "%0." + fieldName, fieldName, elt);
              result.Add(new FieldNode(state, edgname, val));
            }
          }
        }
      }

      return result;
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
    internal readonly Namer namer = new Namer();
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
          vars.Add(vn);
        }
      }

      foreach (var e in dm.model.Elements) {        
        if (e is Model.Number || e is Model.Boolean)
          namer.AddName(e, new EdgeName(e.ToString()));
      }
    } 

    internal void ComputeNames()
    {
      namer.ComputeNames(vars);
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
    protected List<ElementNode> children;

    public ElementNode(StateNode st, IEdgeName name, Model.Element elt)
      : base(name)
    {
      this.stateNode = st;
      this.elt = elt;
    }

    public ElementNode(StateNode st, string name, Model.Element elt)
      : this(st, new EdgeName(name), elt) { }

    public override Model.Element Element
    {
      get
      {
        return elt;
      }
    }

    protected virtual void DoInitChildren()
    {
      children.AddRange(vm.GetExpansion(stateNode, elt));
    }

    protected void InitChildren()
    {
      if (children == null) {
        children = new List<ElementNode>();
        DoInitChildren();
      }
    }

    public override string CanonicalValue
    {
      get
      {
        return stateNode.namer.CanonicalName(Element);
      }
    }

    public override IEnumerable<string> Aliases
    {
      get
      {
        if (Element is Model.Boolean) {
          yield break;
        } else {
          foreach (var edge in stateNode.namer.Aliases(Element))
            if (!edge.Equals(Name))
              yield return edge.FullName();
        }
      }
    }

    public override string ToolTip
    {
      get
      {
        var sb = new StringBuilder();
        int limit = 30;
        foreach (var n in Aliases){
          sb.AppendFormat("   = {0}\n", n); 
          if (limit-- < 0) {
            sb.Append("...");
            break;
          }
        }
        return sb.ToString();
      }
    }

    public override bool Expandable
    {
      get
      {
        InitChildren();
        return children.Count > 0;
      }
    }

    public override IEnumerable<IDisplayNode> Expand()
    {
      InitChildren();
      return children;
    }
  }

  class FieldNode : ElementNode
  {
    public FieldNode(StateNode par, IEdgeName realName, Model.Element elt)
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
    public MapletNode(StateNode par, IEdgeName realName, Model.Element elt)
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
