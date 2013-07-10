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
		protected static Regex bv = new Regex (@"\(_ BitVec (\d+)\)");

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
			newLine = bv.Replace (newLine, "bv${1}");
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

	abstract class ParserSMT : ModelParser
	{
		protected string[] tokens;
		protected List<string> output;
		protected int arity;
		protected int arrayNum;

		abstract protected void ParseArray (ref int i);

		abstract protected void ParseITE (ref int i);

		protected void FindArity ()
		{
			arity = 0;
			int p_count = 1;
			int i = 4;

			while (p_count > 0) {
				if (i == tokens.Length - 1)
					break;
				else if (tokens [i] == ")")
					p_count--;
				else if (tokens [i] == "(" && tokens [i + 1] != "ite") {
					p_count++;
					arity++;
				}

				i++;
			}
		}

		protected string GetValue (int idx)
		{
			string value = tokens [idx];

			if (tokens [idx - 1] == "-") {
				value = "(- " + value + ")";
			} else if (tokens [idx - 2] == "_") {
				value = tokens [idx - 1] + "[" + tokens [idx] + "]";
			}

			return value;
		}

		void ParseEndOfExpression (ref int i)
		{
			i++;

			if (i == tokens.Length && output.Count == 2) {
				i += -2;

				if (tokens [i] == ")") {
					i += -1;
					output.Add (GetValue (i));
				} else {
					output.Add (GetValue (i));
				}
			}

			if (i == tokens.Length && output.Contains ("{")) {
				output.Add (" ");
				output.Add ("}");
			}
		}

		List<string> GetParsedTokens (string newLine)
		{
			if (newLine == null)
				return null;

			newLine = bv.Replace (newLine, "bv${1}");

			string line = newLine;
			int openParenCounter = CountOpenParentheses (newLine, 0);

			while (openParenCounter > 0) {
				newLine = ReadLine ();
				if (newLine == null) {
					return null;
				}
				line += newLine;
				openParenCounter = CountOpenParentheses (newLine, openParenCounter);
			}

			line = line.Replace ("(", " ( ");
			line = line.Replace (")", " ) ");

			tokens = line.Split (seps, StringSplitOptions.RemoveEmptyEntries);
			output = new List<string> ();

			var i = 0;
			bool doneParsing = false;

			while (!doneParsing) {
				switch (tokens [i]) {
				case ")":
					ParseEndOfExpression (ref i);
					break;

				case "define-fun":
					output.Add (GetValue (i + 1));
					output.Add ("->");
					i += 2;
					break;

				case "Array":
					ParseArray (ref i);
					break;

				case "ite":
					ParseITE (ref i);
					break;

				case "_ufmt_1":
				case "x!1":
					output.Add ("{");
					output.Add (" ");
					i++;
					break;

				default:
					i++;
					break;
				}

				if (i == tokens.Length)
					doneParsing = true;
			}

			return output;
		}

		List<string>[] TrySplitExpr (List<string> expr)
		{
			int splits = 1;
			foreach (string tok in expr)
				if (tok.Equals ("@SPLIT"))
					splits++;

			List<string>[] newExpr = new List<string>[splits];

			for (int s = 0; s < splits; s++)
				newExpr [s] = new List<string> ();

			int i = 0;
			foreach (string tok in expr) {
				if (tok.Equals ("@SPLIT")) {
					i++;
					continue;
				}

				newExpr [i].Add (tok);
			}

			return newExpr;
		}

		internal override void Run ()
		{
			var selectFunctions = new Dictionary<int, Model.Func> ();
			var storeFunctions = new Dictionary<int, Model.Func> ();
			arrayNum = 0;

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

				var words = GetParsedTokens (line);
				if (words.Count == 0)
					continue;
				var exprs = TrySplitExpr (words);

				foreach (List<string> expr in exprs) {
					/*Console.WriteLine ("");
					for (int i = 0; i < expr.Count; i++) {
						Console.Write (expr [i] + " ");
					}*/

					var lastToken = expr [expr.Count - 1];
					if (currModel == null)
						BadModel ("model begin marker not found");

					if (expr.Count > 3 && expr [1] == "->") {
						var funName = (string)expr [0];
						Model.Func fn = null;
						int i = 4;

						if (expr [2] != "{" && expr [6] != "{")
							BadModel ("unidentified function definition 5");

						fn = currModel.TryGetFunc (funName);

						for (; ;) {
							if (expr [i] == "}") {
								if (i == expr.Count - 1) {
									if (fn == null)
										fn = currModel.MkFunc (funName, 1);
									break;
								} else {
									i++;
									continue;
								}
							}

							for (; ;) {
								if (expr [i] == " ") {
									i++;
									break;
								}

								if ((i == 4 || i == 8) && expr [i - 1] == " " && expr [i + 1] == " ") {
									if (fn.Else == null)
										fn.Else = GetElt (expr [i]);
									i++;
									continue;
								}

								if (expr [i] == "else") {
									if (expr [i + 1] == "->") {
										i += 2;

										if (expr [i] == "}")
											BadModel ("unidentified function definition 1");

										if (expr [i] == "{") {
											i++;
											continue;
										} else {
											if (fn != null && !(expr [i] == "#unspecified") && fn.Else == null)
												fn.Else = GetElt (expr [i]);
											i++;
											continue;
										}
									} else
										BadModel ("unidentified function definition 2");
								}

								int arity = 0;
								for (; ;) {
									arity++;
									if (expr [arity + i] == " ") {
										arity -= 2;
										break;
									}
								}

								if (expr [i + arity] == "->") {
									i += arity + 1;

									if (expr [i] == "}")
										BadModel ("unidentified function definition 3");
								} else
									BadModel ("unidentified function definition 4");

								if (fn == null) {
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

								for (var idx = 0; idx < fn.Arity; ++idx)
									args [idx] = GetElt (expr [idx + i - arity - 1]);

								fn.AddApp (GetElt (expr [i]), args);

								i++;
								break;
							}
						}
					} else if (expr.Count == 3 && expr [1] == "->") {
						var funName = (string)expr [0];
						Model.Func fn = null;

						fn = currModel.MkFunc (funName, 0);
						fn.SetConstant (GetElt (lastToken));
					} else
						BadModel ("unidentified line");
				}
			}
		}
	}

	internal class ParserZ3_SMTLIB2 : ParserSMT
	{
		protected override void ParseArray (ref int i)
		{
			while (tokens[i] != "as-array")
				i++;

			output.Add ("as-array[" + tokens [i + 1] + "]");
		}

		protected override void ParseITE (ref int i)
		{
			List<string> args = new List<string> ();
			List<string> results = new List<string> ();

			FindArity ();

			for (; ;) {
				i++;

				if (tokens [i] == "=") {
					if (tokens [i + 2] == "(" && tokens [i + 3] == "_") {
						args.Add (GetValue (i + 5));
						i += 6;
					} else if (tokens [i + 2] == "(" && tokens [i + 3] == "-") {
						args.Add (GetValue (i + 4));
						i += 5;
					} else {
						args.Add (GetValue (i + 2));
						i += 3;
					}
				}

				if (args.Count > 0 && args.Count % arity == 0) {
					if (tokens [i + 2] == "(" && tokens [i + 3] == "_") {
						results.Add (GetValue (i + 5));
						i += 6;
					} else if (tokens [i + 2] == "(" && tokens [i + 3] == "-") {
						results.Add (GetValue (i + 4));
						i += 5;
					} else {
						results.Add (GetValue (i + 2));
						i += 3;
					}

					while (i < tokens.Length - 1 && tokens[i + 1] != "=") {
						i++;
					}

					if (i == tokens.Length - 1) {
						while (tokens[i] == ")")
							i += -1;
						results.Add (GetValue (i));
						break;
					}
				}
			}

			int idx = 0;
			for (int j = 0; j < results.Count - 1; j++) {
				for (int r = 0; r < arity; r++) {
					output.Add (args [idx]);
					idx++;
				}

				output.Add ("->");
				output.Add (results [j]);
				output.Add (" ");
			}

			output.Add ("else");
			output.Add ("->");
			output.Add (results [results.Count - 1]);
		}
	}

	internal class ParserCVC4 : ParserSMT
	{
		void SplitArrayExpression ()
		{
			if (output.Contains ("@SPLIT")) {
				output.Add (" ");
				output.Add ("}");
			}

			output.Add ("@SPLIT");
			output.Add ("k!" + arrayNum);
			output.Add ("->");
			output.Add ("{");
			output.Add (" ");

			arrayNum++;
		}

		protected override void ParseArray (ref int i)
		{
			output.Add ("as-array[k!" + arrayNum + "]");
			SplitArrayExpression ();

			while (tokens[i] != "store" && tokens[i] != "__array_store_all__")
				i++;

			if (tokens [i] == "store") {
				List<string> args = new List<string> ();
				int p_count = 1;
				i += 4;

				while (p_count > 0) {
					if (tokens [i] == ")")
						p_count--;
					else if (tokens [i] == "(")
						p_count++;
					i++;
				}

				if (tokens [i] == "(" && tokens [i + 1] == "__array_store_all__") {
					output.Add ("as-array[k!" + arrayNum + "]");
					SplitArrayExpression ();
				} else if (tokens [i] == "(" && tokens [i + 1] == "store") {
					output.Add ("as-array[k!" + arrayNum + "]");
					SplitArrayExpression ();
				} else {
					while (args.Count < 3) {
						if (tokens [i] == ")")
							i++;
						else if (tokens [i] == "(" && tokens [i + 1] == "_") {
							args.Add (GetValue (i + 3));
							i += 5;
						} else if (tokens [i + 1] == "(" && tokens [i + 1] == "-") {
							args.Add (GetValue (i + 2));
							i += 4;
						} else {
							args.Add (GetValue (i));
							i++;
						}
					}

					output.Add (args [1]);
					output.Add ("->");
					output.Add (args [2]);
					output.Add (" ");
					output.Add ("else");
					output.Add ("->");
					output.Add (args [0]);
				}
			} else if (tokens [i] == "__array_store_all__") {
				int p_count = 1;
				i += 2;

				while (p_count > 0) {
					if (tokens [i] == ")")
						p_count--;
					else if (tokens [i] == "(")
						p_count++;
					i++;
				}

				if (tokens [i] == "(" && tokens [i + 1] == "_") {
					output.Add (GetValue (i + 3));
					i += 5;
				} else if (tokens [i] == "(" && tokens [i + 1] == "-") {
					output.Add (GetValue (i + 2));
					i += 4;
				} else {
					output.Add (GetValue (i));
					i++;
				}
			}
		}
		/*
		protected override void ParseArray(ref int i)
		{
			output.Add("as-array[k!" + arrayNum + "]");
			output.Add("@SPLIT");
			output.Add("k!" + arrayNum);
			output.Add("->");
			output.Add("{");
			output.Add(" ");

			while (tokens[i] != "store" && tokens[i] != "__array_store_all__")
				i++;

			if (tokens[i] == "store")
			{
				List<string> args = new List<string>();
				int p_count = 1;
				i += 4;

				while (p_count > 0)
				{
					if (tokens[i] == ")")
						p_count--;
					else if (tokens[i] == "(")
						p_count++;
					i++;
				}

				while(args.Count < 3)
				{
					if (tokens[i] == ")")
						i++;
					else if (tokens[i] == "(" && tokens[i + 1] == "_")
					{
						args.Add(GetValue(i + 3));
						i += 5;
					}
					else if (tokens[i + 1] == "(" && tokens[i + 1] == "-")
					{
						args.Add(GetValue(i + 2));
						i += 4;
					}
					else
					{
						args.Add(GetValue(i));
						i++;
					}
				}

				output.Add(args[1]);
				output.Add("->");
				output.Add(args[2]);
				output.Add(" ");
				output.Add("else");
				output.Add("->");
				output.Add(args[0]);
			}
			else if (tokens[i] == "__array_store_all__")
			{
				int p_count = 1;
				i += 2;

				while (p_count > 0)
				{
					if (tokens[i] == ")")
						p_count--;
					else if (tokens[i] == "(")
						p_count++;
					i++;
				}

				if (tokens[i] == "(" && tokens[i + 1] == "_")
				{
					output.Add(GetValue(i + 3));
					i += 5;
				}
				else if (tokens[i] == "(" && tokens[i + 1] == "-")
				{
					output.Add(GetValue(i + 2));
					i += 4;
				}
				else
				{
					output.Add(GetValue(i));
					i++;
				}
			}
		}
		*/
		protected override void ParseITE (ref int i)
		{
			List<string> args = new List<string> ();
			List<string> results = new List<string> ();

			FindArity ();

			int occurrences = 0;

			foreach (string tok in tokens) {
				if (tok == "_ufmt_1")
					occurrences++;
			}

			for (; ;) {
				i++;

				if (tokens [i] == "=") {
					if (tokens [i + 2] == "(" && tokens [i + 3] == "_") {
						args.Add (GetValue (i + 5));
						i += 6;
					} else if (tokens [i + 2] == "(" && tokens [i + 3] == "-") {
						args.Add (GetValue (i + 4));
						i += 5;
					} else {
						args.Add (GetValue (i + 2));
						i += 2;
					}
				}

				if ((args.Count > 0 && args.Count % arity == 0) ||
					(results.Count > 0 && occurrences <= 2)) {
					if (tokens [i + 2] == "(" && tokens [i + 3] == "_") {
						results.Add (GetValue (i + 5));
						i += 6;
					} else if (tokens [i + 2] == "(" && tokens [i + 3] == "-") {
						results.Add (GetValue (i + 4));
						i += 5;
					} else {
						results.Add (GetValue (i + 2));
						i += 2;
					}

					while (i < tokens.Length - 1 && tokens[i + 1] != "=") {
						i++;
					}

					if (i == tokens.Length - 1) {
						while (tokens[i] == ")")
							i += -1;
						results.Add (GetValue (i));
						break;
					}
				}
			}

			int idx = 0;

			for (int j = 0; j < results.Count - 1; j++) {
				if (occurrences > 2) {
					for (int r = 0; r < arity; r++) {
						output.Add (args [idx]);
						idx++;
					}
				} else {
					if (arity == 1) {
						output.Add (args [idx]);
						idx++;
					} else {
						output.Add (args [0]);

						for (int r = 1; r < arity; r++) {
							idx++;
							output.Add (args [idx]);
						}
					}
				}

				output.Add ("->");
				output.Add (results [j]);
				output.Add (" ");
			}

			output.Add ("else");
			output.Add ("->");
			output.Add (results [results.Count - 1]);
		}
	}
}
