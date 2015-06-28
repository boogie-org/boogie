open System
open Microsoft.FSharp.Text.Lexing

open System.IO

open ForroPrinter
open Resolver
open Lexer
open Parser
open BoogiePrinter

open Translator

let readAndProcess tracing (filename: string) =
    try
        if tracing then printfn "Forró: version 1.0" else ()
        // lex
        let f = if filename = null then Console.In else new StreamReader(filename) :> TextReader
        let lexbuf = LexBuffer<char>.FromTextReader(f)
        lexbuf.EndPos <- { pos_bol = 0;
                           pos_fname=if filename = null then "stdin" else filename; 
                           pos_cnum=0;
                           pos_lnum=1 }
        // parse
        let prog = Parser.start Lexer.tokenize lexbuf
        // print the given Forró program
        if tracing then
            printfn "---------- Given Forró program ----------"
            Print prog
        else ()
        // make sure the program is legal
        let rprog = Resolve prog
        // translate into Boogie
        let bprog = Translate rprog
        // print the Boogie program
        if tracing then printfn "---------- Resulting Boogie program ----------" else ()
        BPrint bprog
        // that's it
        if tracing then printfn "----------" ; printfn "Done" else ()

    with
     | ResolutionError(msg) ->
        printfn "Resolution error: %s" msg            
     | ex ->
        printfn "Unhandled Exception: %s" ex.Message

let rec start n (args: string []) tracing filename =
  if n < args.Length then
    let arg = args.[n]
    if arg = "/break" then ignore (System.Diagnostics.Debugger.Launch()) else ()
    let filename = if arg.StartsWith "/" then filename else arg
    start (n+1) args (tracing || arg = "/trace") filename
  else
    readAndProcess tracing filename

let args = Environment.GetCommandLineArgs()
start 1 args false null
