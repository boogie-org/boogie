using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer.Vcc
{
  public class Provider : ILanguageProvider
  {
    public static Provider Instance = new Provider();
    private Provider() { }

    public bool IsMyModel(Model m)
    {
      return m.TryGetFunc("$is_ghost_field") != null && m.TryGetFunc("$fk_vol_version") != null;
    }

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m)
    {
      var vm = new VccModel(m);
      foreach (var s in m.States) {
        var sn = new StateNode(vm.states.Count, vm, s);
        vm.states.Add(sn);
      }
      return vm;
    }
  }

  enum DataKind
  {
    Flat,
    PhysPtr,
    SpecPtr,
    Map
  }

  class VccModel : LanguageModel
  {
    public readonly Model model;
    public readonly Model.Func f_ptr_to, f_phys_ptr_cast, f_spec_ptr_cast, f_mathint, f_local_value_is, f_spec_ptr_to, f_heap, f_select_field,
                               f_select_value, f_field, f_field_type, f_int_to_ptr, f_ptr_to_int, f_ptr, f_map_t;
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();

    public VccModel(Model m)
    {
      model = m;
      f_ptr_to = m.MkFunc("$ptr_to", 1);
      f_spec_ptr_to = m.MkFunc("$spec_ptr_to", 1);
      f_phys_ptr_cast = m.MkFunc("$phys_ptr_cast", 2);
      f_spec_ptr_cast = m.MkFunc("$spec_ptr_cast", 2);
      f_mathint = m.MkFunc("^^mathint", 0);
      f_local_value_is = m.MkFunc("$local_value_is", 5);
      f_heap = m.MkFunc("$heap", 1);
      f_select_field = m.MkFunc("Select_[$field][$ptr]$int", 2);
      f_select_value = m.MkFunc("Select_[$ptr]$int", 2);
      f_field = m.MkFunc("$field", 1);
      f_field_type = m.MkFunc("$field_type", 1);
      f_int_to_ptr = m.MkFunc("$int_to_ptr", 1);
      f_ptr_to_int = m.MkFunc("$ptr_to_int", 1);
      f_ptr = m.MkFunc("$ptr", 2);
      f_map_t = m.MkFunc("$map_t", 2);
    }

    public string GetUserVariableName(string name)
    {
      if (name.StartsWith("L#") || name.StartsWith("P#"))
        return name.Substring(2);
      return null;
    }

    public Model.Element LocalType(string localName)
    {
      var v = GetUserVariableName(localName);
      if (v == null) v = localName;
      var c = model.TryGetFunc("#loc." + v);
      if (c != null) {
        var localIs = f_local_value_is.AppWithArg(2, c.GetConstant());
        if (localIs != null)
          return localIs.Args[4];
      }
      return f_mathint.GetConstant();
    }

    public Model.Element Image(Model.Element elt, Model.Func f)
    {
      var r = f.AppWithResult(elt);
      if (r != null)
        return r.Args[0];
      return null;
    }

    string TypeNameCore(Model.Element elt)
    {
      var deref = Image(elt, f_ptr_to);
      if (deref != null)
        return TypeName(deref) + "*";
      deref = Image(elt, f_spec_ptr_to);
      if (deref != null)
        return TypeName(deref) + "^";
      var mapt = f_map_t.AppWithResult(elt);
      if (mapt != null)
        return string.Format("{1}[{0}]", TypeName(mapt.Args[0]), TypeName(mapt.Args[1]));

      foreach (var app in elt.Names)
        if (app.Func.Arity == 0 && app.Func.Name.StartsWith("^")) {
          var n = app.Func.Name.Substring(1); 
          switch (n) {
            case "^i1": return "int8_t";
            case "^u1": return "uint8_t";
            case "^i2": return "int16_t";
            case "^u2": return "uint16_t";
            case "^i4": return "int32_t";
            case "^u4": return "uint32_t";
            case "^i8": return "int64_t";
            case "^u8": return "uint64_t";
            case "^bool": return "bool";
            default: return n;
          }          
        }
      return elt.ToString();
    }

    public string TypeName(Model.Element elt)
    {
      string res;
      if (!typeName.TryGetValue(elt, out res)) {
        typeName[elt] = elt.ToString(); // avoid infinite recursion
        res = TypeNameCore(elt);
        typeName[elt] = res;
      }
      return res;
    }

    public static readonly string[] synthethic_fields = new string[] { "$f_owns", "$f_ref_cnt", "$f_vol_version", "$f_root", "$f_group_root" };

    public string ConstantFieldName(Model.Element elt)
    {
      var bestScore = int.MaxValue;
      string bestName = null;

      foreach (var t in elt.Names) {
        var score = int.MaxValue;
        string name = null;
        if (t.Args.Length == 0) {
          name = t.Func.Name;
          score = 0;
          var dotIdx = name.IndexOf('.');
          if (dotIdx > 0) {
            score += 10;
            name = name.Substring(dotIdx + 1);
          }
          if (name.Contains('#')) score -= 1;
        } else if (synthethic_fields.Contains(t.Func.Name)) {
          name = string.Format("{0}<{1}>", t.Func.Name.Substring(3), TypeName(t.Args[0]));
          score = 5;
        }
        if (score < bestScore) {
          bestScore = score;
          bestName = name;
        }
      }

      return bestName;
    }

    public DataKind GetKind(Model.Element tp, out Model.FuncTuple tpl)
    {
      tpl = f_ptr_to.AppWithResult(tp);
      if (tpl != null) return DataKind.PhysPtr;
      tpl = f_spec_ptr_to.AppWithResult(tp);
      if (tpl != null) return DataKind.SpecPtr;
      tpl = f_map_t.AppWithResult(tp);
      if (tpl != null) return DataKind.Map;
      return DataKind.Flat;
    }

    public DataKind GetKind(Model.Element tp)
    {
      Model.FuncTuple dummy;
      return GetKind(tp, out dummy);
    }


    public Model.Element WrapForUse(Model.Element elt, Model.Element tp)
    {
      Model.FuncTuple tpl;
      var kind = GetKind(tp, out tpl);

      if (kind == DataKind.Flat) return elt;

      if (kind == DataKind.Map) {
        if (elt.Kind == Model.ElementKind.Integer) {
          Model.Element theMap = null;
          foreach (var conv in model.Functions)
            // really, we should reconstruct the name of this function, but this is painful
            if (conv.Arity == 1 && conv.Name.StartsWith("$int_to_map_t")) {
              var app = conv.AppWithArg(0, elt);
              if (app != null) {
                theMap = app.Result;          
                break;
              }
            }
          if (theMap == null) return elt;
          return theMap;
        }
        return elt;
      }

      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr) {
        if (elt.Kind == Model.ElementKind.Integer) {
          var tmp = f_int_to_ptr.TryEval(elt);
          if (tmp != null)
            elt = tmp;
        }
      }

      if (kind == DataKind.PhysPtr)
        return Util.OrElse(f_phys_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      if (kind == DataKind.SpecPtr)
        return Util.OrElse(f_spec_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      Util.Assert(false);
      return elt;
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt, Model.Element tp)
    {
      List<ElementNode> result = new List<ElementNode>();
      Model.FuncTuple tpl;

      var kind = GetKind(tp, out tpl);
      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr) {
        var heap = state.state.TryGet("$s");
        if (heap != null)
          heap = f_heap.TryEval(heap);
        if (heap != null) {
          foreach (var fld in f_select_field.AppsWithArg(0, heap)) {
            var val = f_select_value.TryEval(fld.Result, elt);
            if (val != null) {
              var ftp = f_field_type.TryEval(fld.Args[1]);
              val = WrapForUse(val, ftp);
              var nm = ConstantFieldName(fld.Args[1]);
              var edgname = nm == null ? new EdgeName(fld.Args[1].ToString()) : new EdgeName(this, nm);
              result.Add(new FieldNode(state, edgname, val, ftp));
            }
          }
          //result.Sort(CompareFields);
        }
      } else if (kind == DataKind.Map) {
        var elTp = tpl.Args[1];
        foreach (var sel in model.Functions)
          if (sel.Arity == 2 && sel.Name.StartsWith("$select.$map_t")) {
            foreach (var app in sel.AppsWithArg(0, elt)) {
              var val = WrapForUse(app.Result, elTp);
              var edgname = new EdgeName(this, "[%0]", app.Args[1]);
              result.Add(new MapletNode(state, edgname, val, elTp));
            }
          }
      }

      return result;
    }

    public override IEnumerable<IState> States
    {
      get
      {
        return states;
      }
    }

    protected override string CanonicalBaseName(Model.Element elt)
    {
      var vm = this;
      var name = base.CanonicalBaseName(elt);

      if (name.Contains("[") || name.Contains("'") || name.Contains("-"))
        name = "";

      if (name != "")
        return name;

      foreach (var tpl in elt.References) {
        var fn = tpl.Func;
        if (fn.Name.StartsWith("$select.$map_t") && fn.Arity == 2 && tpl.Args[0] == elt)
          return "map";
        if (fn.Name.StartsWith("$int_to_map_t") && tpl.Result == elt)
          return "map";
      }

      var fld = vm.f_field.TryEval(elt);
      if (fld != null) {
        var tp = vm.f_field_type.TryEval(fld);
        if (tp != null) {
          return vm.TypeName(tp);
        }
      }

      // return elt.ToString(); // for debugging
      return "";
    }
  }

  class StateNode : IState
  {
    internal Model.CapturedState state;
    string name;
    internal VccModel vm;
    internal List<VariableNode> vars;
    internal int index;
    
    public StateNode(int i, VccModel parent, Model.CapturedState s)
    {
      this.vm = parent;
      state = s;
      index = i;

      name = s.Name;
      var idx = name.LastIndexOfAny(new char[] { '\\', '/' });
      if (idx > 0)
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
      if (vars != null) return;
      vars = new List<VariableNode>();

      var names = Util.Empty<string>();

      if (vm.states.Count > 0) {
        var prev = vm.states.Last();
        names = prev.vars.Map(v => v.realName);
      }

      names = names.Concat(state.Variables).Distinct();

      var curVars = state.Variables.ToDictionary(x => x);
      foreach (var v in names) {
        if (vm.GetUserVariableName(v) != null) {
          var tp = vm.LocalType(v);
          var val = state.TryGet(v);
          val = vm.WrapForUse(val, tp);
          var vn = new VariableNode(this, v, val, tp);
          vn.updatedHere = vm.states.Count > 0 && curVars.ContainsKey(v);
          if (curVars.ContainsKey(v))
            vm.RegisterLocalValue(vn.Name, val);
          vars.Add(vn);
        }
      }

      vm.Flush(vars);
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
    protected Model.Element tp;
    protected VccModel vm { get { return stateNode.vm; } }

    public ElementNode(StateNode st, EdgeName name, Model.Element elt, Model.Element tp)
      : base(st.vm, name, elt)
    {
      this.stateNode = st;
      this.tp = tp;
    }

    public ElementNode(StateNode st, string name, Model.Element elt, Model.Element tp)
      : this(st, new EdgeName(name), elt, tp) { }

    protected override void ComputeChildren()
    {
      children.AddRange(vm.GetExpansion(stateNode, element, tp));
    }

    public override string ToolTip
    {
      get
      {
        var sb = new StringBuilder();
        sb.AppendFormat("Type: {0}\n", vm.TypeName(tp));
        /*
        int limit = 30;
        foreach (var n in Aliases){
          sb.AppendFormat("   = {0}\n", n); 
          if (limit-- < 0) {
            sb.Append("...");
            break;
          }
        }
         */
        return sb.ToString();
      }
    }
  }

  class FieldNode : ElementNode
  {
    public FieldNode(StateNode par, EdgeName realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
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
    public MapletNode(StateNode par, EdgeName realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
    {
    }
  }

  class VariableNode : ElementNode
  {
    public bool updatedHere;
    public string realName;

    public VariableNode(StateNode par, string realName, Model.Element elt, Model.Element tp)
      : base(par, realName, elt, tp)
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
