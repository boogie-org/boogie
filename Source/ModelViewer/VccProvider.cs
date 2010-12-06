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

    public ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts)
    {
      var vm = new VccModel(m, opts);
      return vm;
    }
  }

  enum DataKind
  {
    Flat,
    PhysPtr,
    SpecPtr,
    Object,
    Ptrset,
    Map
  }

  class VccModel : LanguageModel
  {
    public readonly Model model;
    public readonly Model.Func f_ptr_to, f_phys_ptr_cast, f_spec_ptr_cast, f_mathint, f_local_value_is, f_spec_ptr_to, f_heap, f_select_field,
                               f_select_value, f_field, f_field_type, f_int_to_ptr, f_ptr_to_int, f_ptr, f_map_t, f_select_ptr,
                               f_owners, f_closed, f_roots, f_timestamps, f_select_bool, f_select_int, f_is_null, f_good_state,
                               f_int_to_version, f_int_to_ptrset, f_set_in0, f_is_ghost_field, f_is_phys_field;
    public readonly Model.Element tp_object, tp_mathint, tp_bool, tp_state, tp_ptrset;
    public readonly Model.Element elt_me, elt_null;
    Dictionary<Model.Element, string> typeName = new Dictionary<Model.Element, string>();
    Dictionary<Model.Element, string> literalName = new Dictionary<Model.Element, string>();
    public List<StateNode> states = new List<StateNode>();
    public readonly ViewOptions viewOpts;

    public VccModel(Model m, ViewOptions opts)
    {
      viewOpts = opts;
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
      f_select_ptr = m.MkFunc("Select_[$ptr]$ptr", 2);
      f_select_int = m.MkFunc("Select_[$ptr]$int", 2);
      f_select_bool = m.MkFunc("Select_[$ptr]$bool", 2);
      f_owners = m.MkFunc("$f_owner", 1);
      f_closed = m.MkFunc("$f_closed", 1);
      f_roots = m.MkFunc("$roots", 1);
      f_timestamps = m.MkFunc("$f_timestamp", 1);
      f_field = m.MkFunc("$field", 1);
      f_field_type = m.MkFunc("$field_type", 1);
      f_int_to_ptr = m.MkFunc("$int_to_ptr", 1);
      f_ptr_to_int = m.MkFunc("$ptr_to_int", 1);
      f_ptr = m.MkFunc("$ptr", 2);
      f_map_t = m.MkFunc("$map_t", 2);
      f_is_null = m.MkFunc("$is_null", 1);
      f_good_state = m.MkFunc("$good_state", 1);
      f_int_to_version = m.MkFunc("$int_to_version", 1);
      f_int_to_ptrset = m.MkFunc("$int_to_ptrset", 1);
      f_set_in0 = m.MkFunc("$set_in0", 2);
      f_is_ghost_field = m.MkFunc("$is_ghost_field", 1);
      f_is_phys_field = m.MkFunc("$is_phys_field", 1);

      tp_bool = m.GetFunc("^^bool").GetConstant();
      tp_mathint = m.GetFunc("^^mathint").GetConstant();
      tp_object = m.GetFunc("^^object").GetConstant();
      tp_state = m.GetFunc("^$#state_t").GetConstant();
      tp_ptrset = m.GetFunc("^$#ptrset").GetConstant();

      elt_me = m.GetFunc("$me").GetConstant();
      elt_null = m.GetFunc("$null").GetConstant();

      literalName[elt_me] = "\\me";
      literalName[elt_null] = "NULL";
      foreach (var tpl in f_phys_ptr_cast.Apps) {
        if (tpl.Args[0] == elt_null)
          literalName[tpl.Result] = "(" + TypeName(tpl.Args[1]) + "*)NULL";
      }
      foreach (var tpl in f_spec_ptr_cast.Apps) {
        if (tpl.Args[0] == elt_null)
          literalName[tpl.Result] = "(" + TypeName(tpl.Args[1]) + "^)NULL";
      }
      foreach (var fn in model.Functions) {
        if (fn.Arity == 0 && fn.Name.StartsWith("l#"))
          literalName[fn.GetConstant()] = ":" + fn.Name.Substring(2);
      }

      var idx = 0;
      foreach (var s in m.States) {
        var elt = s.TryGet("$s");
        if (elt != null)
          literalName[elt] = "\\state'" + idx;
        idx++;
      }

      foreach (var s in m.States) {
        var sn = new StateNode(states.Count, this, s);
        states.Add(sn);
      }
    }

    #region Function name scoring
    static string[][] prefixes = new string[][] {
      new string[] { "F#", "$eq.$map", },
      new string[] { "#lambda", },
      new string[] { "$int_to_", "lambda@", "distinct-aux-f", "Select_","Store_", "$select.", "$store.", },
    };

    static string[][] totals = new string[][] {
      new string[] {
      "$addr", "$current_timestamp", 
      "$full_stop", "$function_entry", "$ptr_to_i4",
      "$ptr_to_i8", "$ptr_to_u4", "$ptr_to_u8", 
      "$span", "$sizeof", "$in_domain", 
      "$inv2", 
      "$is_claimable", 
      "$set_cardinality", "$set_difference", "$set_union",
      "$thread_local", "$unchecked", "$writes_at", 
      },

      new string[] {
      "$dot", "$emb0", "$fetch_from_domain", "$in_range_phys_ptr",
      "$in_range_spec_ptr", "$is_sequential_field", "$is_volatile_field",
      "$is_ghost_field", "$is_phys_field", "$is_math_type", "$invok_state",
      "$is_primitive",
      "$spec_ptr_cast",
      "$phys_ptr_cast", 
      "$is_null", 
      "$in_domain_lab",
      "$inv_lab", 
      "$set_in0", 
      },

      new string[] {
      "$_pow2", "$as_composite_field", "$as_field_with_type", "$as_in_range_t",
      "$as_primitive_field", "$base", "$call_transition", "tickleBool", "Ctor",
      "@MV_state", "$field", "$field_arr_root", "$field_kind", "$field_offset",
      "$field_parent_type", "$field_type", "$file_name_is", "$good_state",
      "$good_state_ext", "$function_arg_type", "$has_field_at0", "$map_domain",
      "$map_range", "$map_t", "$ptr_to", "$ptr_to_i1", "$ptr_to_i2",
      "$ptr_to_u1", "$ptr_to_u2", "$is_unwrapped", "$is_unwrapped_dynamic",
      "$heap", "$closed", "$owner", "$owns", "$modifies", "$post_unwrap",
      "$pow2", "$pre_unwrap", "$ptr", "$is", "$in_range_t", "$roots",
      "$timestamp", "$type_branch", "$type_code_is", "$type_project_0",
      "$typemap", "$set_in_pos", "$updated_owns", "$ver_domain", "$vs_state",
      "$set_singleton",
      "$f_owner", "$f_closed", "$f_timestamps",
      "$local_value_is",
      "$field_arr_ctor",
      },
    };

    string[] state_props = new string[] { };

    Dictionary<string, int> functionScores = new Dictionary<string, int>();

    int FunctionScore(string name)
    {
      if (functionScores.Count == 0) {
        for (int i = 0; i < totals.Length; ++i)
          foreach (var s in totals[i])
            functionScores[s] = i;
      }

      int res;
      if (functionScores.TryGetValue(name, out res))
        return res;

      res = -1;
      if (name[0] == '$' && name.EndsWith("_to_int"))
        res = 1;
      else {
        for (int i = 0; i < prefixes.Length; ++i)
          foreach (var p in prefixes[i])
            if (name.StartsWith(p)) {
              res = i;
              goto stop;
            }
      stop: ;
      }

      if (res == -1)
        res = 1; // default

      functionScores[name] = res;
      return res;
    }
    #endregion

    public string GetUserVariableName(string name)
    {
      if (name.StartsWith("L#") || name.StartsWith("P#"))
        return name.Substring(2);
      return null;
    }

    protected override string LiteralName(Model.Element elt)
    {
      string r;

      if (literalName.TryGetValue(elt, out r))
        return r;

      r = TryTypeName(elt);
      if (r != null) {
        literalName[elt] = r;
        return r;
      }

      return base.LiteralName(elt);
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

      return null;
    }

    public string TypeName(Model.Element elt)
    {
      var r = TryTypeName(elt);
      if (r == null)
        return elt.ToString();
      else return r;
    }

    public string TryTypeName(Model.Element elt)
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

    bool IsState(Model.Element elt)
    {
      return GuessType(elt) == tp_state;
    }

    Model.Element GuessType(Model.Element element)
    {
      if (element is Model.Boolean)
        return tp_bool;

      foreach (var tpl in element.References) {
        if (element == tpl.Result) {
          if (tpl.Func == f_ptr)
            return tp_object;
        }

        if (tpl.Args.Length >= 1 && tpl.Args[0] == element) {
          if (tpl.Func == f_heap || tpl.Func == f_closed || tpl.Func == f_good_state)
            return tp_state;
        }
      }

      return tp_mathint;
    }

    public DataKind GetKind(Model.Element tp, out Model.FuncTuple tpl)
    {
      tpl = null;

      if (tp == tp_object)
        return DataKind.Object;
      else if (tp == tp_ptrset)
        return DataKind.Ptrset;
      
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
      } else if (kind == DataKind.Ptrset) {
        var tmp = f_int_to_ptrset.TryEval(elt);
        if (tmp != null)
          return tmp;
        return elt;
      }

      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr || kind == DataKind.Object) {
        if (elt.Kind == Model.ElementKind.Integer) {
          var tmp = f_int_to_ptr.TryEval(elt);
          if (tmp != null)
            elt = tmp;
        }
      }

      if (kind == DataKind.Object)
        return elt;

      if (kind == DataKind.PhysPtr)
        return Util.OrElse(f_phys_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      if (kind == DataKind.SpecPtr)
        return Util.OrElse(f_spec_ptr_cast.TryEval(elt, tpl.Args[0]), elt);

      Util.Assert(false);
      return elt;
    }

    void AddSpecialField(StateNode state, Model.Element elt, List<ElementNode> res, string name, Model.Func select_map)
    {
      var map = state.state.TryGet("$s");
      if (map != null)
        map = select_map.TryEval(map);
      if (map != null) {
        var model = elt.Model;
        Model.Element val = f_select_bool.TryEval(map, elt);
        Model.Element tp = tp_bool;
        if (val == null) {
          val = f_select_ptr.TryEval(map, elt);
          tp = tp_object;
        }
        if (val == null) {
          val = f_select_int.TryEval(map, elt);
          tp = tp_mathint;
        }
        if (val != null) {
          res.Add(new FieldNode(state, new EdgeName(name), val, tp) { Category = NodeCategory.MethodologyProperty });
        }
      }
    }

    public IEnumerable<ElementNode> GetExpansion(StateNode state, Model.Element elt, Model.Element tp)
    {
      List<ElementNode> result = new List<ElementNode>();
      Model.FuncTuple tpl;

      var kind = GetKind(tp, out tpl);
      if (kind == DataKind.PhysPtr || kind == DataKind.SpecPtr || kind == DataKind.Object) {
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

              var cat = NodeCategory.PhysField;
              if (f_is_ghost_field.IsTrue(fld.Args[1]))
                cat = NodeCategory.SpecField;
              if (nm != null && nm.Contains("<"))
                cat = NodeCategory.MethodologyProperty;
              result.Add(new FieldNode(state, edgname, val, ftp) { Category = cat });
            }
          }

          AddSpecialField(state, elt, result, "\\closed", f_closed);
          AddSpecialField(state, elt, result, "\\owner", f_owners);
          AddSpecialField(state, elt, result, "\\root", f_roots);
          AddSpecialField(state, elt, result, "\\timestamp", f_timestamps);

          //result.Sort(CompareFields);
        }
      } else if (kind == DataKind.Map) {
        var elTp = tpl.Args[1];
        foreach (var sel in model.Functions)
          if (sel.Arity == 2 && sel.Name.StartsWith("$select.$map_t")) {
            foreach (var app in sel.AppsWithArg(0, elt)) {
              var val = WrapForUse(app.Result, elTp);
              var edgname = new EdgeName(this, "[%0]", app.Args[1]);
              result.Add(new MapletNode(state, edgname, val, elTp) { Category = NodeCategory.Maplet });
            }
          }
      } else if (kind == DataKind.Ptrset) {
        foreach (var sel in f_select_bool.AppsWithArg(0, elt)) {
          var edgname = new EdgeName(this, "[%0]", sel.Args[1]);
          result.Add(new MapletNode(state, edgname, sel.Result, tp_bool) { Category = NodeCategory.Maplet });
        }
      }

      if (!(elt is Model.Boolean)) {
        var curState = state.state.TryGet("$s");
        foreach (var tupl in elt.References) {
          if (!tupl.Args.Contains(elt)) continue; // not looking for aliases (maybe we should?)
          if (tupl.Args.Any(IsState) && !tupl.Args.Contains(curState))
            continue;          
          var argsFmt = new StringBuilder();
          var name = tupl.Func.Name;
          var cat = NodeCategory.MethodologyProperty;
          if (name.StartsWith("F#")) {
            name = name.Substring(2);
            cat = NodeCategory.UserFunction;
          }
          argsFmt.Append(name).Append("(");
          var args = new List<Model.Element>();
          foreach (var a in tupl.Args) {
            if (a == curState)
              argsFmt.Append("\\now, ");
            else if (a == elt)
              argsFmt.Append("*, ");
            else {
              argsFmt.AppendFormat("%{0}, ", args.Count);
              args.Add(a);
            }
          }
          argsFmt.Length -= 2;
          argsFmt.Append(")");
          var edgeName = new EdgeName(this, argsFmt.ToString(), args.ToArray());
          result.Add(new MapletNode(state, edgeName, tupl.Result, GuessType(tupl.Result)) { ViewLevel = FunctionScore(tupl.Func.Name), Category = cat });
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

        if (fn.Arity >= 1 && tpl.Args[0] == elt) {
          if (fn == f_select_bool)
            return "ptrset";
        }

        if (tpl.Result == elt)
          if (fn == f_int_to_version)
            return "version";
      }

      var fld = vm.f_field.TryEval(elt);
      if (fld != null) {
        var tp = vm.f_field_type.TryEval(fld);
        if (tp != null) {
          return vm.TypeName(tp);
        }
      }

      if (viewOpts.DebugMode)
        return elt.ToString();
      else
        return "";
    }

    public override string PathName(IEnumerable<IDisplayNode> path)
    {
      var sb = new StringBuilder();
      foreach (var d in path) {
        var name = d.Name;
        if (name == "") continue; // can that happen?
        if (sb.Length > 0 && name[0] != '[')
          sb.Append("->");
        sb.Append(d.Name);
      }

      return sb.ToString();
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
      var limit = 30;
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
  }
}
