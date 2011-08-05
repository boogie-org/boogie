using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer.BCT {
  public class Provider : ILanguageProvider {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m) {
      return m.TryGetFunc("Alloc") != null;
    }

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts) {
      var dm = new BCTModel(m, opts);
      foreach (var s in m.States) {
        var sn = new StateNode(dm.states.Count, dm, s);
        dm.states.Add(sn);
      }
      dm.FinishStates();
      return dm;
    }
  }

  class BCTModel : LanguageModel {
    public readonly Model.Func f_heap_select;
    public readonly Dictionary<Model.Element, Model.Element[]> ArrayLengths = new Dictionary<Model.Element, Model.Element[]>();
    public readonly Dictionary<Model.Element, Model.FuncTuple> DatatypeValues = new Dictionary<Model.Element, Model.FuncTuple>();
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();

    public BCTModel(Model m, ViewOptions opts)
      : base(m, opts) {
      f_heap_select = m.MkFunc("[3]", 3);
    }

    internal void FinishStates() {
      GenerateSourceLocations(states);
    }

    public override IEnumerable<IState> States {
      get { return states; }
    }

    public string GetUserVariableName(string name) {
      if (name.StartsWith("$")) 
        return null;
      var hash = name.IndexOf('#');
      if (0 < hash)
        return name.Substring(0, hash);
      return name;
    }

    public Model.Element Image(Model.Element elt, Model.Func f) {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }
    /*
    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt) {
      List<ElementNode> result = new List<ElementNode>();

      if (elt.Kind != Model.ElementKind.Uninterpreted)
        return result;

      // Perhaps elt is a known datatype value
      Model.FuncTuple fnTuple;
      if (DatatypeValues.TryGetValue(elt, out fnTuple)) {
        // elt is a datatype value
        int i = 0;
        foreach (var arg in fnTuple.Args) {
          var edgname = new EdgeName(this, i.ToString());
          result.Add(new FieldNode(state, edgname, arg));
          i++;
        }
        return result;
      }

      // Perhaps elt is a sequence
      var seqLen = f_seq_length.AppWithArg(0, elt);
      if (seqLen != null) {
        // elt is a sequence
        foreach (var tpl in f_seq_index.AppsWithArg(0, elt)) {
          var edgname = new EdgeName(this, "[%0]", tpl.Args[1]);
          result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
        }
        return result;
      }

      // Perhaps elt is a set
      foreach (var tpl in f_set_select.AppsWithArg(0, elt)) {
        var setElement = tpl.Args[1];
        var containment = tpl.Result;
        var edgname = new EdgeName(this, "[%0]", Unbox(setElement));
        result.Add(new FieldNode(state, edgname, containment));
      }
      if (result.Count != 0)
        return result;  // elt is a set

      // It seems elt is an object or array
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
      var heap = state.State.TryGet("$Heap");
      if (heap != null) {
        foreach (var tpl in f_heap_select.AppsWithArgs(0, heap, 1, elt)) {
          var field = new FieldName(tpl.Args[2], this);
          if (field.NameFormat != "alloc") {
            var edgname = new EdgeName(this, field.NameFormat, field.NameArgs);
            result.Add(new FieldNode(state, edgname, Unbox(tpl.Result)));
          }
        }
      }
      return result;
    }
     */ 
  }

  class StateNode : NamedState {
    internal readonly BCTModel dm;
    internal readonly List<VariableNode> vars = new List<VariableNode>();
    internal readonly int index;

    public StateNode(int i, BCTModel parent, Model.CapturedState s)
      : base(s, parent) {
      dm = parent;
      state = s;
      index = i;

      SetupVars();
    }

    void SetupVars() {
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

      dm.Flush(Nodes);
    }

    public override IEnumerable<IDisplayNode> Nodes {
      get {
        return vars;
      }
    }
  }

  class ElementNode : DisplayNode {
    protected StateNode stateNode;
    protected Model.Element elt;
    protected BCTModel vm { get { return stateNode.dm; } }

    public ElementNode(StateNode st, EdgeName name, Model.Element elt)
      : base(st.dm, name, elt) {
      this.stateNode = st;
      this.elt = elt;
    }

    public ElementNode(StateNode st, string name, Model.Element elt)
      : this(st, new EdgeName(name), elt) { }

    protected override void ComputeChildren() {
      //children.AddRange(vm.GetExpansion(stateNode, elt));
    }
  }

  class VariableNode : ElementNode {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt)
      : base(par, realName, elt) {
      this.realName = realName;
      name = new EdgeName(vm.GetUserVariableName(realName));
    }
  }
}
