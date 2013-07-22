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

	class ParserSMT : ModelParser
	{
		string[] tokens;
		List<string> output;
		int arity;
		int arrayNum;
		int index;

		void FindArity ()
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

		string GetValue (int idx)
		{
			string value = tokens [idx];

			if (tokens [idx - 1] == "-") {
				value = "(- " + value + ")";
			} else if (tokens [idx - 2] == "_") {
				value = tokens [idx - 1] + "[" + tokens [idx] + "]";
			}

			return value;
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

		void SplitArrayExpression ()
		{
			output.Add ("as-array[k!" + arrayNum + "]");

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

		void ParseArrayExpr ()
		{
			while (tokens [index] != "as-array" && tokens [index] != "store" && tokens [index] != "__array_store_all__")
				index++;

			if (tokens [index] == "store") {
				SplitArrayExpression ();

				List<string> args = new List<string> ();
				int p_count = 1;
				index += 4;

				while (p_count > 0) {
					if (tokens [index] == ")")
						p_count--;
					else if (tokens [index] == "(")
						p_count++;
					index++;
				}

				if ((tokens [index] == "(" && tokens [index + 1] == "__array_store_all__") ||
					(tokens [index] == "(" && tokens [index + 1] == "store")) {
					SplitArrayExpression ();
				} else {
					while (args.Count < 3) {
						if (tokens [index] == ")")
							index++;
						else if (tokens [index] == "(") {
							while (tokens [index] != ")")
								index++;
							args.Add (GetValue (index - 1));
						} else {
							args.Add (GetValue (index));
						}

						index++;
					}

					output.Add (args [1]);
					output.Add ("->");
					output.Add (args [2]);
					output.Add (" ");
					output.Add ("else");
					output.Add ("->");
					output.Add (args [0]);
				}
			} else if (tokens [index] == "__array_store_all__") {
				SplitArrayExpression ();

				while (tokens[index] == "__array_store_all__") {
					int p_count = 1;
					index += 2;

					while (p_count > 0) {
						if (tokens [index] == ")")
							p_count--;
						else if (tokens [index] == "(")
							p_count++;
						index++;
					}

					if (tokens [index] == "(" && tokens [index + 1] == "__array_store_all__") {
						SplitArrayExpression ();
						index++;
					} else {
						if (tokens [index] == ")")
							index++;
						else if (tokens [index] == "(") {
							while (tokens [index] != ")")
								index++;
							output.Add (GetValue (index - 1));
						} else {
							output.Add (GetValue (index));
						}

						index++;
					}
				}
			} else if (tokens [index] == "as-array") {
				output.Add ("as-array[" + tokens [index + 1] + "]");
			}
		}

		void ParseIteExpr ()
		{
			List<string> args = new List<string> ();
			List<string> results = new List<string> ();

			FindArity ();

			for (; ;) {
				index++;

				if (tokens [index] == "=") {
					while (tokens[index] != ")")
						index++;
					args.Add (GetValue (index - 1));
				}

				if (args.Count > 0 && args.Count % arity == 0) {
					while (tokens[index] == ")")
						index++;

					if (tokens [index] == "(") {
						while (tokens[index] != ")")
							index++;
						results.Add (GetValue (index - 1));
					} else {
						results.Add (GetValue (index));
					}

					while (index < tokens.Length - 1 && tokens[index + 1] != "=")
						index++;

					if (index == tokens.Length - 1) {
						while (tokens[index] == ")")
							index += -1;
						results.Add (GetValue (index));
						break;
					}
				}
			}

			int i = 0;

			for (int j = 0; j < results.Count - 1; j++) {
				for (int r = 0; r < arity; r++) {
					output.Add (args [i]);
					i++;
				}

				output.Add ("->");
				output.Add (results [j]);
				output.Add (" ");
			}

			output.Add ("else");
			output.Add ("->");
			output.Add (results [results.Count - 1]);
		}

		void ParseEndOfExpr ()
		{
			index++;

			if (index == tokens.Length && output.Count == 2) {
				index += -2;

				if (tokens [index] == ")") {
					index += -1;
					output.Add (GetValue (index));
				} else {
					output.Add (GetValue (index));
				}
			}

			if (index == tokens.Length && output.Contains ("{")) {
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

			index = 0;
			bool doneParsing = false;

			while (!doneParsing) {
				switch (tokens [index]) {
				case ")":
					ParseEndOfExpr ();
					break;

				case "define-fun":
					output.Add (GetValue (index + 1));
					output.Add ("->");
					index += 2;
					break;

				case "_ufmt_1":
				case "x!1":
					output.Add ("{");
					output.Add (" ");
					if (Array.IndexOf (tokens, "ite") > -1)
						ParseIteExpr ();
					else
						index++;
					break;

				case "Array":
					ParseArrayExpr ();
					break;

				default:
					index++;
					break;
				}

				if (index == tokens.Length)
					doneParsing = true;
			}

			return output;
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

//				Console.WriteLine("\n\n# :: " + line);

				var words = GetParsedTokens (line);
				if (words.Count == 0)
					continue;
				var exprs = TrySplitExpr (words);

				foreach (List<string> expr in exprs) {
//					Console.WriteLine ("");
//					for (int i = 0; i < expr.Count; i++) {
//						Console.Write (expr [i] + " ");
//					}

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
}
