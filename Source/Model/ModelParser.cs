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
		internal List<Model> resModels = new List<Model>();
		internal System.IO.TextReader rd;

		string lastLine = "";
		protected static char[] seps = new char[] { ' ' };
		protected static Regex bv = new Regex(@"\(_ BitVec (\d+)\)");

		protected void NewModel()
		{
			lastLine = "";
			currModel = new Model();
			resModels.Add(currModel);
		}

		protected void BadModel(string msg)
		{
			throw new ArgumentException(string.Format("Invalid model: {0}, at line {1} ({2})", msg, lineNo, lastLine));
		}

		protected string ReadLine()
		{
			var l = rd.ReadLine();
			if (l != null) {
				lineNo++;
				lastLine = l;
			}
			return l;
		}

		string[] GetWords(string line)
		{
			if (line == null)
				return null;
			var words = line.Split(seps, StringSplitOptions.RemoveEmptyEntries);
			return words;
		}

		Model.Element GetElt(string name) {
			Model.Element ret = currModel.TryMkElement(name);
			if (ret == null)
				BadModel("invalid element name " + name);
			return ret;
		}

		protected Model.Element GetElt(object o) {
			string s = o as string;
			if (s != null)
				return GetElt(s);
			List<object> os = (List<object>)o;
			List<Model.Element> args = new List<Model.Element>();
			for (int i = 1; i < os.Count; i++) {
				args.Add(GetElt(os[i]));
			}
			return new Model.DatatypeValue(currModel, (string)os[0], args);
		}

		protected int CountOpenParentheses(string s, int n)
		{
			int f = n;
			foreach (char c in s) {
				if (c == '(')
					f++;
				else if (c == ')')
					f--;
			}
			if (f < 0) BadModel("mismatched parentheses in datatype term");
			return f;
		}

		abstract internal void Run();
	}

	class ParserZ3_2 : ModelParser
	{
		List<object> GetFunctionTokens(string newLine)
		{
			if (newLine == null)
				return null;
			newLine = bv.Replace(newLine, "bv${1}");
			string line = newLine;
			int openParenCounter = CountOpenParentheses(newLine, 0);
			if (!newLine.Contains("}"))
			{
				while (openParenCounter > 0)
				{
					newLine = ReadLine();
					if (newLine == null)
					{
						return null;
					}
					line += newLine;
					openParenCounter = CountOpenParentheses(newLine, openParenCounter);
				}
			}

			line = line.Replace("(", " ( ");
			line = line.Replace(")", " ) ");
			var tuple = line.Split(seps, StringSplitOptions.RemoveEmptyEntries);

			List<object> newTuple = new List<object>();
			Stack<List<object>> wordStack = new Stack<List<object>>();
			for (int i = 0; i < tuple.Length; i++)
			{
				string elem = tuple[i];
				if (elem == "(")
				{
					List<object> ls = new List<object>();
					wordStack.Push(ls);
				}
				else if (elem == ")")
				{
					List<object> ls = wordStack.Pop();
					if (wordStack.Count > 0)
					{
						wordStack.Peek().Add(ls);
					}
					else
					{
						newTuple.Add(ls);
					}
				}
				else if (wordStack.Count > 0)
				{
					wordStack.Peek().Add(elem);
				}
				else
				{
					newTuple.Add(elem);
				}
			}
			return newTuple;
		}

		internal override void Run()
		{
			var selectFunctions = new Dictionary<int, Model.Func>();
			var storeFunctions = new Dictionary<int, Model.Func>();
			for (; ; ) {
				var line = ReadLine();
				if (line == null) break; // end of model, everything fine

				if (line == "Counterexample:" || line == "Error model: " || line == "*** MODEL") {
					NewModel();
					continue;
				}

				if (line.EndsWith(": Invalid.") || line.EndsWith(": Valid.")|| line.StartsWith("labels:"))
					continue;
				if (line == "END_OF_MODEL" || line == "." || line == "*** END_MODEL")
					continue;

				var words = GetFunctionTokens(line);

				Console.WriteLine("");
				for (int i = 0; i < words.Count; i++)
				{
					Console.Write(words[i] + " ");
				}

				if (words.Count == 0) continue;
				var lastWord = words[words.Count - 1];

				if (currModel == null)
					BadModel("model begin marker not found");

				if (line.StartsWith("*** STATE ")) {
					var name = line.Substring(10);
					Model.CapturedState cs;
					if (name == "<initial>")
						cs = currModel.InitialState;
					else
						cs = currModel.MkState(name);
					for (; ; ) {
						var tmpline = ReadLine();
						if (tmpline == "*** END_STATE") break;
						var tuple = GetFunctionTokens(tmpline);
						if (tuple == null) BadModel("EOF in state table");
						if (tuple.Count == 0) continue;
						if (tuple.Count == 3 && tuple[0] is string && tuple[1] is string && ((string) tuple[1]) == "->")
						{
							cs.AddBinding((string)tuple[0], GetElt(tuple[2]));
						}
						else
						{
							BadModel("invalid state tuple definition");
						}
					}
					continue;
				}

				if (words.Count == 3 && words[1] is string && ((string) words[1]) == "->") {
					var funName = (string) words[0];
					Model.Func fn = null;

					if (lastWord is string && ((string) lastWord) == "{") {
						fn = currModel.TryGetFunc(funName);
						for ( ; ; ) {
							var tuple = GetFunctionTokens(ReadLine());

							Console.WriteLine("");
							for (int i = 0; i < tuple.Count; i++)
							{
								Console.Write(tuple[i] + " ");
							}

							if (tuple == null) BadModel("EOF in function table");
							if (tuple.Count == 0) continue;
							string tuple0 = tuple[0] as string;
							if (tuple.Count == 1) {
								if (fn == null)
									fn = currModel.MkFunc(funName, 1);
								if (tuple0 == "}") break;
								if (fn.Else == null)
									fn.Else = GetElt(tuple[0]);
								continue;
							}
							string tuplePenultimate = tuple[tuple.Count - 2] as string;
							if (tuplePenultimate != "->") BadModel("invalid function tuple definition");
							var resultName = tuple[tuple.Count - 1];
							if (tuple0 == "else") {
								if (fn != null && !(resultName is string && ((string)resultName) == "#unspecified") && fn.Else == null) {
									fn.Else = GetElt(resultName);
								}
								continue;
							}

							if (fn == null) {
								var arity = tuple.Count - 2;
								if (Regex.IsMatch(funName, "^MapType[0-9]*Select$")) {
									funName = string.Format("[{0}]", arity);
									if (!selectFunctions.TryGetValue(arity, out fn)) {
										fn = currModel.MkFunc(funName, arity);
										selectFunctions.Add(arity, fn);
									}
								} else if (Regex.IsMatch(funName, "^MapType[0-9]*Store$")) {
									funName = string.Format("[{0}:=]", arity);
									if (!storeFunctions.TryGetValue(arity, out fn)) {
										fn = currModel.MkFunc(funName, arity);
										storeFunctions.Add(arity, fn);
									}
								} else {
									fn = currModel.MkFunc(funName, arity);
								}
							}
							var args = new Model.Element[fn.Arity];
							for (int i = 0; i < fn.Arity; ++i)
								args[i] = GetElt(tuple[i]);
							fn.AddApp(GetElt(resultName), args);
						}
					} else {
						fn = currModel.MkFunc(funName, 0);
						fn.SetConstant(GetElt(lastWord));
					}
				} else {
					BadModel("unidentified line");
				}
			}
		}
	}

	abstract class ParserSMT : ModelParser
	{
		protected string[] tokens;
		protected List<string> output;

		protected string GetValue(int idx)
		{
			string value = tokens[idx];

			if (tokens[idx - 1] == "-")
			{
				value = "(- " + value + ")";
			}
			else if (tokens[idx - 2] == "_")
			{
				value = tokens[idx - 1] + "[" + tokens[idx] + "]";
			}

			return value;
		}

		abstract protected void ParseLeftParenthesis(ref int i);
		abstract protected void ParseITE(ref int i);
		abstract protected void ParseArray(ref int i);

		void ParseEqual(ref int i)
		{
			i += 3;
			output.Add(GetValue(i));
			output.Add("->");
			i += 2;
			output.Add(GetValue(i));
			output.Add(" ");
			output.Add("else");
			output.Add("->");
			i++;
		}

		protected void ParseBitVector(ref int i)
		{
			i++;

			if (tokens[i] == "BitVec")
			{
				output.Add("->");
				i += 3;
			}

			if (tokens[i].Contains("bv"))
			{
				output.Add(GetValue(i + 1));
				i += 2;
			}
		}

		void ParseDefineFun(ref int i)
		{
			i++;

			output.Add(GetValue(i));
			output.Add("->");

			i++;
		}

		void ParseRightParenthesis(ref int i)
		{
			i++;

			if (i == tokens.Length && output.Count == 2)
			{
				i += -2;

				if (tokens[i] == ")")
				{
					i += -1;
					output.Add(GetValue(i));
				}
				else
				{
					output.Add(GetValue(i));
				}
			}

			if (i == tokens.Length && output.Contains("{"))
			{
				output.Add(" ");
				output.Add("}");
			}
		}

		void ParseTokens()
		{
			var i = 0;
			bool doneParsing = false;

			while(!doneParsing)
			{
				switch (tokens[i])
				{
				case ")":
					ParseRightParenthesis(ref i);
					break;

				case "(":
					ParseLeftParenthesis(ref i);
					break;

				case "declare-sort":
					doneParsing = true;
					break;

				case "define-fun":
					ParseDefineFun(ref i);
					break;

				default:
					i++;
					break;
				}

				if (i == tokens.Length)
					doneParsing = true;
			}
		}

		protected List<string> GetParsedTokens(string newLine)
		{
			if (newLine == null)
				return null;

			newLine = bv.Replace(newLine, "bv${1}");

			string line = newLine;
			int openParenCounter = CountOpenParentheses(newLine, 0);

			while (openParenCounter > 0)
			{
				newLine = ReadLine();
				if (newLine == null)
				{
					return null;
				}
				line += newLine;
				openParenCounter = CountOpenParentheses(newLine, openParenCounter);
			}

			line = line.Replace("(", " ( ");
			line = line.Replace(")", " ) ");

			tokens = line.Split(seps, StringSplitOptions.RemoveEmptyEntries);
			output = new List<string>();
			ParseTokens();

			return output;
		}
	}

	internal class ParserZ3 : ParserSMT
	{
		protected override void ParseITE(ref int i)
		{
			for (; ; )
			{
				if (tokens[i] == "ite")
				{
					i++;

					for (; ; )
					{
						if (tokens[i] == "(" && tokens[i + 1] == "and")
							i += 2;

						if (tokens[i] == "(" && tokens[i + 1] == "=")
						{
							if (tokens[i + 3] == "(" && tokens[i + 4] == "-")
							{
								i += 7;
								output.Add(GetValue(i - 2));
							}
							if (tokens[i + 3] == "(" && tokens[i + 4] == "_")
							{
								i += 8;
								output.Add(GetValue(i - 2));
							}
							else
							{
								i += 4;
								output.Add(GetValue(i - 1));
							}

							i++;
							continue;
						}

						output.Add("->");

						if (tokens[i] == ")") i++;

						if (tokens[i] == "(" && tokens[i + 1] == "-")
						{
							i += 3;
							output.Add(GetValue(i - 1));
						}
						else if (tokens[i] == "(" && tokens[i + 1] == "_")
						{
							i += 4;
							output.Add(GetValue(i - 1));
						}
						else
						{
							i++;
							output.Add(GetValue(i - 1));
						}

						output.Add(" ");
						break;
					}
				}

				if (tokens[i] == "(" && tokens[i + 1] == "-")
				{
					i += 2;
					output.Add("else");
					output.Add("->");
					output.Add(GetValue(i));
					break;
				}
				else if (tokens[i] == "(" && tokens[i + 1] == "_")
				{
					i += 3;
					output.Add("else");
					output.Add("->");
					output.Add(GetValue(i));
					break;
				}
				else if (tokens[i] == ")" && tokens[i - 2] == "-")
				{
					i++;
					continue;
				}
				else if (tokens[i] == ")" && tokens[i - 3] == "_")
				{
					i++;
					continue;
				}
				else if (tokens[i] != "(")
				{
					output.Add("else");
					output.Add("->");
					output.Add(GetValue(i));
					break;
				}
				else i++;
			}
		}

		void ParseArgument(ref int i)
		{
			output.Add("{");
			output.Add(" ");

			i++;
		}


		protected override void ParseArray(ref int i)
		{
			while (tokens[i] != "as-array")
				i++;

			output.Add("as-array[" + tokens[i + 1] + "]");
		}

		protected override void ParseLeftParenthesis(ref int i)
		{
			i++;

			switch (tokens[i])
			{
			case "ite":
				ParseITE(ref i);
				break;

			case "Array":
				ParseArray(ref i);
				break;

			case "x!1":
				ParseArgument(ref i);
				break;

			case "_":
				ParseBitVector(ref i);
				break;

			default:
				break;
			}
		}

		internal override void Run()
		{
			var selectFunctions = new Dictionary<int, Model.Func>();
			var storeFunctions = new Dictionary<int, Model.Func>();

			for (; ; )
			{
				var line = ReadLine();
				if (line == null) break; // end of model, everything fine
				if (line == "Counterexample:" || line == "Error model: " || line == "*** MODEL")
				{
					NewModel();
					continue;
				}
				if (line.EndsWith(": Invalid.") || line.EndsWith(": Valid.")|| line.StartsWith("labels:"))
					continue;
				if (line == "END_OF_MODEL" || line == "." || line == "*** END_MODEL")
					continue;

				var words = GetParsedTokens(line);

				Console.WriteLine("");
				for (int i = 0; i < words.Count; i++)
				{
					Console.Write(words[i] + " ");
				}

				if (words.Count == 0) continue;
				var lastToken = words[words.Count - 1];
				if (currModel == null)
					BadModel("model begin marker not found");

				if (words.Count > 3 && words[1] == "->")
				{
					var funName = (string) words[0];
					Model.Func fn = null;

					if (words[2] != "{")
						BadModel("unidentified function definition 5");

					fn = currModel.TryGetFunc(funName);

					int i = 4;
					for (; ; )
					{
						if (words[i] == "}")
						{
							if (i == words.Count - 1)
							{
								if (fn == null)
									fn = currModel.MkFunc(funName, 1);
								break;
							}
							else
							{
								i++;
								continue;
							}
						}

						for (; ; )
						{
							if (words[i] == " ")
							{
								i++;
								break;
							}

							if (i == 4 && words[3] == " " && words[5] == " ") {
								if (fn == null)
									fn = currModel.MkFunc(funName, 1);
								if (fn.Else == null)
									fn.Else = GetElt(words[i]);
								i++;
								continue;
							}

							if (words[i] == "else")
							{
								if (words[i + 1] == "->")
								{
									i += 2;

									if (words[i] == "}")
										BadModel("unidentified function definition 1");

									if (words[i] == "{")
									{
										i++;
										continue;
									}
									else
									{
										if (fn != null && !(words[i] == "#unspecified") && fn.Else == null)
											fn.Else = GetElt(words[i]);
										i++;
										continue;
									}
								}
								else
									BadModel("unidentified function definition 2");
							}

							int arity = 0;
							for (; ; )
							{
								arity++;
								if (words[arity + i] == " ")
								{
									arity -= 2;
									break;
								}
							}

							if (words[i + arity] == "->")
							{
								i += arity + 1;

								if (words[i] == "}")
									BadModel("unidentified function definition 3");
							}
							else
								BadModel("unidentified function definition 4");

							if (fn == null)
							{
								if (Regex.IsMatch(funName, "^MapType[0-9]*Select$"))
								{
									funName = string.Format("[{0}]", arity);

									if (!selectFunctions.TryGetValue(arity, out fn))
									{
										fn = currModel.MkFunc(funName, arity);
										selectFunctions.Add(arity, fn);
									}
								}
								else if (Regex.IsMatch(funName, "^MapType[0-9]*Store$"))
								{
									funName = string.Format("[{0}:=]", arity);

									if (!storeFunctions.TryGetValue(arity, out fn)) {
										fn = currModel.MkFunc(funName, arity);
										storeFunctions.Add(arity, fn);
									}
								}
								else
								{
									fn = currModel.MkFunc(funName, arity);
								}
							}

							var args = new Model.Element[fn.Arity];

							for (var idx = 0; idx < fn.Arity; ++idx)
								args[idx] = GetElt(words[idx + i - arity - 1]);

							fn.AddApp(GetElt(words[i]), args);

							i++;
							break;
						}
					}
				}
				else if (words.Count == 3 && words[1] == "->")
				{
					var funName = (string) words[0];
					Model.Func fn = null;

					fn = currModel.MkFunc(funName, 0);
					fn.SetConstant(GetElt(lastToken));
				}
				else
					BadModel("unidentified line");
			}
		}
	}

	internal class ParserCVC4 : ParserSMT
	{
		int arrayNum;
		int arity;

		void FindArity()
		{
			arity = 0;
			int p_count = 1;
			int i = 4;

			while (p_count > 0)
			{
				if (i == tokens.Length - 1)
					break;
				else if (tokens[i] == ")")
					p_count--;
				else if (tokens[i] == "(" && tokens[i + 1] != "ite")
				{
					p_count++;
					arity++;
				}

				i++;
			}
		}
		/*
		protected override void ParseITE(ref int i)
		{
			List<string> args = new List<string>();
			List<string> results = new List<string>();

			FindArity();

			output.Add("{");
			output.Add(" ");

			for (; ; )
			{
				if (tokens[i] == ")")
				{
					if ((tokens[i + 1] == ")" || tokens[i + 2] == ")") &&
					    (tokens[i + 2] != "ite" || tokens[i + 3] != "ite") &&
					    (tokens[i - 3] == "_" || tokens[i - 2] == "-"))
					{
						results.Add(GetValue(i - 1));
						break;
					}
					else
					{
						args.Add(GetValue(i - 1));

						if (tokens[i + 1] == "(" && tokens[i + 2] == "-")
						{
							results.Add(GetValue(i + 3));
							i += 5;
						}
						else if (tokens[i + 2] != "ite")
						{
							results.Add(GetValue(i + 1));
							i += 2;
						}
						else i++;
					}
				}
				else i++;
			}

			int idx = 0;
			for (int j = 0; j < results.Count - 1; j++)
			{
				if (arity == 1)
				{
					output.Add(args[idx]);
					idx++;
				}
				else
				{
					output.Add(args[0]);

					for (int r = 1; r < arity; r++)
					{
						idx++;
						output.Add(args[idx]);
					}
				}

				output.Add("->");
				output.Add(results[j]);
				output.Add(" ");
			}

			output.Add("else");
			output.Add("->");
			output.Add(results[results.Count - 1]);
		}
		*/
		protected override void ParseITE(ref int i)
		{
			List<string> args = new List<string>();
			List<string> results = new List<string>();

			FindArity();

			output.Add("{");
			output.Add(" ");

			for (; ; )
			{
				i++;

				if (tokens[i] == ")")
				{
					if (((tokens[i + 1] == ")" && tokens[i + 3] != "ite") ||
					    (tokens[i + 2] == ")" && tokens[i + 4] != "ite")) &&
					    args.Count % arity == 0)
					{
						Console.WriteLine("Res(*): " + GetValue(i - 1));
						results.Add(GetValue(i - 1));
						break;
					}

					if (tokens[i - 3] == "=" || tokens[i - 5] == "=" || tokens[i - 6] == "=")
					{
						Console.WriteLine("Arg: " + GetValue(i - 1));
						args.Add(GetValue(i - 1));
					}

					if (tokens [i + 1] == ")") i += 2;
					else i++;

					if (tokens[i] == "(" && tokens[i + 1] == "-")
					{
						Console.WriteLine("Res: " + GetValue(i + 2));
						results.Add(GetValue(i + 2));
						i += 4;
					}
					else if (tokens[i] == "(" && tokens[i + 1] == "_")
					{
						Console.WriteLine("Res: " + GetValue(i + 3));
						results.Add(GetValue(i + 3));
						i += 5;
					}
					else if (tokens[i] != "(")
					{
						Console.WriteLine("Res: " + GetValue(i));
						results.Add(GetValue(i));
						i++;
					}
				}
			}

			int idx = 0;
			for (int j = 0; j < results.Count - 1; j++)
			{
				for (int r = 0; r < arity; r++)
				{
					output.Add(args[idx]);
					idx++;
				}

				output.Add("->");
				output.Add(results[j]);
				output.Add(" ");
			}

			output.Add("else");
			output.Add("->");
		}

		protected override void ParseArray(ref int i)
		{
			output.Add("as-array[k!" + arrayNum + "]");
			output.Add("@SPLIT");
			output.Add("k!" + arrayNum);
			output.Add("->");
			output.Add("{");
			output.Add(" ");

			for (; ; )
			{
				i++;

				if (tokens[i] == "store")
				{
					while (tokens[i] != ",")
						i++;

					output.Add(GetValue(i + 10));
					output.Add("->");
					output.Add(GetValue(i + 15));
					output.Add(" ");
					output.Add("else");
					output.Add("->");
					output.Add(GetValue(i + 4));

					i += 15;

					break;
				}
				else if (tokens[i] == ",")
				{
					i += 2;
					ParseBitVector(ref i);
					break;
				}
			}
		}

		protected override void ParseLeftParenthesis(ref int i)
		{
			i++;

			switch (tokens[i])
			{
			case "ite":
				ParseITE(ref i);
				break;

			case "Array":
				ParseArray(ref i);
				break;

			case "_":
				ParseBitVector(ref i);
				break;

			default:
				break;
			}
		}

		internal override void Run()
		{
			var selectFunctions = new Dictionary<int, Model.Func>();
			var storeFunctions = new Dictionary<int, Model.Func>();
			arrayNum = 0;

			for (; ; )
			{
				var line = ReadLine();
				if (line == null) break; // end of model, everything fine
				if (line == "Counterexample:" || line == "Error model: " || line == "*** MODEL")
				{
					NewModel();
					continue;
				}
				if (line.EndsWith(": Invalid.") || line.EndsWith(": Valid.")|| line.StartsWith("labels:"))
					continue;
				if (line == "END_OF_MODEL" || line == "." || line == "*** END_MODEL")
					continue;

				var words = GetParsedTokens(line);

				Console.WriteLine("");
				for (int i = 0; i < words.Count; i++)
				{
					Console.Write(words[i] + " ");
				}

				if (words.Count == 0) continue;
				var lastToken = words[words.Count - 1];
				if (currModel == null)
					BadModel("model begin marker not found");

				if (words.Count > 3 && words[1] == "->")
				{
					var funName = (string) words[0];
					Model.Func fn = null;
					int i = 4;

					if (words.Contains("@SPLIT"))
					{
						arrayNum++;

						fn = currModel.MkFunc(funName, 0);
						fn.SetConstant(GetElt(words[2]));

						i = 8;

						funName = (string) words[4];
						fn = null;
					}

					if (words[2] != "{" && words[6] != "{")
						BadModel("unidentified function definition 5");

					fn = currModel.TryGetFunc(funName);

					for (; ; )
					{
						if (words[i] == "}")
						{
							if (i == words.Count - 1)
							{
								if (fn == null)
									fn = currModel.MkFunc(funName, 1);
								break;
							}
							else
							{
								i++;
								continue;
							}
						}

						for (; ; )
						{
							if (words[i] == " ")
							{
								i++;
								break;
							}

							if ((i == 4 || i == 8)  && words[i - 1] == " " && words[i + 1] == " ") {
								if (fn.Else == null)
									fn.Else = GetElt(words[i]);
								i++;
								continue;
							}

							if (words[i] == "else")
							{
								if (words[i + 1] == "->")
								{
									i += 2;

									if (words[i] == "}")
										BadModel("unidentified function definition 1");

									if (words[i] == "{")
									{
										i++;
										continue;
									}
									else
									{
										if (fn != null && !(words[i] == "#unspecified") && fn.Else == null)
											fn.Else = GetElt(words[i]);
										i++;
										continue;
									}
								}
								else
									BadModel("unidentified function definition 2");
							}

							int arity = 0;
							for (; ; )
							{
								arity++;
								if (words[arity + i] == " ")
								{
									arity -= 2;
									break;
								}
							}

							if (words[i + arity] == "->")
							{
								i += arity + 1;

								if (words[i] == "}")
									BadModel("unidentified function definition 3");
							}
							else
								BadModel("unidentified function definition 4");

							if (fn == null)
							{
								if (Regex.IsMatch(funName, "^MapType[0-9]*Select$"))
								{
									funName = string.Format("[{0}]", arity);

									if (!selectFunctions.TryGetValue(arity, out fn))
									{
										fn = currModel.MkFunc(funName, arity);
										selectFunctions.Add(arity, fn);
									}
								}
								else if (Regex.IsMatch(funName, "^MapType[0-9]*Store$"))
								{
									funName = string.Format("[{0}:=]", arity);

									if (!storeFunctions.TryGetValue(arity, out fn)) {
										fn = currModel.MkFunc(funName, arity);
										storeFunctions.Add(arity, fn);
									}
								}
								else
								{
									fn = currModel.MkFunc(funName, arity);
								}
							}

							var args = new Model.Element[fn.Arity];

							for (var idx = 0; idx < fn.Arity; ++idx)
								args[idx] = GetElt(words[idx + i - arity - 1]);

							fn.AddApp(GetElt(words[i]), args);

							i++;
							break;
						}
					}
				}
				else if (words.Count == 3 && words[1] == "->")
				{
					var funName = (string) words[0];
					Model.Func fn = null;

					fn = currModel.MkFunc(funName, 0);
					fn.SetConstant(GetElt(lastToken));
				}
				else
					BadModel("unidentified line");
			}
		}
	}
}
