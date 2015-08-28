//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace Microsoft.Boogie
{
	abstract internal class ModelParser
	{
		protected Model currModel;
		int lineNo;
		internal List<Model> resModels = new List<Model> ();
		internal System.IO.TextReader rd;
		string lastLine = "";
		protected static char[] seps = new char[] { ' ' };
		protected static Regex bitVec = new Regex (@"\(_ BitVec (\d+)\)");
		protected static Regex bv = new Regex (@"\(_ bv(\d+) (\d+)\)");

		protected void NewModel ()
		{
			lastLine = "";
			currModel = new Model ();
			resModels.Add (currModel);
		}

		protected void BadModel (string msg)
		{
			throw new ArgumentException (string.Format ("Invalid model: {0}, at line {1} ({2})", msg, lineNo, lastLine));
		}

		protected string ReadLine ()
		{
			var l = rd.ReadLine ();
			if (l != null) {
				lineNo++;
				lastLine = l;
			}
			return l;
		}

		string[] GetWords (string line)
		{
			if (line == null)
				return null;
			var words = line.Split (seps, StringSplitOptions.RemoveEmptyEntries);
			return words;
		}

		Model.Element GetElt (string name)
		{
			Model.Element ret = currModel.TryMkElement (name);
			if (ret == null)
				BadModel ("invalid element name " + name);
			return ret;
		}

		protected Model.Element GetElt (object o)
		{
			string s = o as string;
			if (s != null)
				return GetElt (s);
			List<object> os = (List<object>)o;
            if (!(os[0] is string))
                os.Insert(0, "_");  // KLM: fix crash on ((as const (Array Int Int)) 0)
			List<Model.Element> args = new List<Model.Element> ();
			for (int i = 1; i < os.Count; i++) {
				args.Add (GetElt (os [i]));
			}
			return new Model.DatatypeValue (currModel, (string)os [0], args);
		}

		protected int CountOpenParentheses (string s, int n)
		{
			int f = n;
			foreach (char c in s) {
				if (c == '(')
					f++;
				else if (c == ')')
					f--;
			}
			if (f < 0)
				BadModel ("mismatched parentheses in datatype term");
			return f;
		}

		abstract internal void Run ();
	}

	class ParserZ3 : ModelParser
	{
		List<object> GetFunctionTokens (string newLine)
		{
			if (newLine == null)
				return null;
			newLine = bitVec.Replace (newLine, "bv${1}");
			newLine = bv.Replace (newLine, "bv${1}[${2}]");
			string line = newLine;
			int openParenCounter = CountOpenParentheses (newLine, 0);
			if (!newLine.Contains ("}")) {
				while (openParenCounter > 0) {
					newLine = ReadLine ();
					if (newLine == null) {
						return null;
					}
					line += newLine;
					openParenCounter = CountOpenParentheses (newLine, openParenCounter);
				}
			}

			line = line.Replace ("(", " ( ");
			line = line.Replace (")", " ) ");
			var tuple = line.Split (seps, StringSplitOptions.RemoveEmptyEntries);

			List<object> newTuple = new List<object> ();
			Stack<List<object>> wordStack = new Stack<List<object>> ();
			for (int i = 0; i < tuple.Length; i++) {
				string elem = tuple [i];
				if (elem == "(") {
					List<object> ls = new List<object> ();
					wordStack.Push (ls);
				} else if (elem == ")") {
					List<object> ls = wordStack.Pop ();
					if (wordStack.Count > 0) {
						wordStack.Peek ().Add (ls);
					} else {
						newTuple.Add (ls);
					}
				} else if (wordStack.Count > 0) {
					wordStack.Peek ().Add (elem);
				} else {
					newTuple.Add (elem);
				}
			}
			return newTuple;
		}

		internal override void Run ()
		{
			var selectFunctions = new Dictionary<int, Model.Func> ();
			var storeFunctions = new Dictionary<int, Model.Func> ();
			for (; ;) {
				var line = ReadLine ();
				if (line == null)
					break; // end of model, everything fine

				if (line == "Counterexample:" || line == "Error model: " || line == "*** MODEL") {
					NewModel ();
					continue;
				}

				if (line.EndsWith (": Invalid.") || line.EndsWith (": Valid.") || line.StartsWith ("labels:"))
					continue;
				if (line == "END_OF_MODEL" || line == "." || line == "*** END_MODEL")
					continue;

				var words = GetFunctionTokens (line);
				if (words.Count == 0)
					continue;
				var lastWord = words [words.Count - 1];

				if (currModel == null)
					BadModel ("model begin marker not found");

				if (line.StartsWith ("*** STATE ")) {
					var name = line.Substring (10);
					Model.CapturedState cs;
					if (name == "<initial>")
						cs = currModel.InitialState;
					else
						cs = currModel.MkState (name);
					for (; ;) {
						var tmpline = ReadLine ();
						if (tmpline == "*** END_STATE")
							break;
						var tuple = GetFunctionTokens (tmpline);
						if (tuple == null)
							BadModel ("EOF in state table");
						if (tuple.Count == 0)
							continue;
						if (tuple.Count == 3 && tuple [0] is string && tuple [1] is string && ((string)tuple [1]) == "->") {
							cs.AddBinding ((string)tuple [0], GetElt (tuple [2]));
						} else {
							BadModel ("invalid state tuple definition");
						}
					}
					continue;
				}

				if (words.Count == 3 && words [1] is string && ((string)words [1]) == "->") {
					var funName = (string)words [0];
					Model.Func fn = null;

					if (lastWord is string && ((string)lastWord) == "{") {
						fn = currModel.TryGetFunc (funName);
						for (; ;) {
							var tuple = GetFunctionTokens (ReadLine ());
							if (tuple == null)
								BadModel ("EOF in function table");
							if (tuple.Count == 0)
								continue;
							string tuple0 = tuple [0] as string;
							if (tuple.Count == 1) {
								if (fn == null)
									fn = currModel.MkFunc (funName, 1);
								if (tuple0 == "}")
									break;
								if (fn.Else == null)
									fn.Else = GetElt (tuple [0]);
								continue;
							}
							string tuplePenultimate = tuple [tuple.Count - 2] as string;
							if (tuplePenultimate != "->")
								BadModel ("invalid function tuple definition");
							var resultName = tuple [tuple.Count - 1];
							if (tuple0 == "else") {
								if (fn != null && !(resultName is string && ((string)resultName) == "#unspecified") && fn.Else == null) {
									fn.Else = GetElt (resultName);
								}
								continue;
							}

							if (fn == null) {
								var arity = tuple.Count - 2;
								if (Regex.IsMatch (funName, "^MapType[0-9]*Select$")) {
									funName = string.Format ("[{0}]", arity);
									if (!selectFunctions.TryGetValue (arity, out fn)) {
										fn = currModel.MkFunc (funName, arity);
										selectFunctions.Add (arity, fn);
									}
								} else if (Regex.IsMatch (funName, "^MapType[0-9]*Store$")) {
									funName = string.Format ("[{0}:=]", arity);
									if (!storeFunctions.TryGetValue (arity, out fn)) {
										fn = currModel.MkFunc (funName, arity);
										storeFunctions.Add (arity, fn);
									}
								} else {
									fn = currModel.MkFunc (funName, arity);
								}
							}
							var args = new Model.Element[fn.Arity];
							for (int i = 0; i < fn.Arity; ++i)
								args [i] = GetElt (tuple [i]);
							fn.AddApp (GetElt (resultName), args);
						}
					} else {
						fn = currModel.MkFunc (funName, 0);
						fn.SetConstant (GetElt (lastWord));
					}
				} else {
					BadModel ("unidentified line");
				}
			}
		}
	}

}
