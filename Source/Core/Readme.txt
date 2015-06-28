// ----------------------------------------------------------------------------
//  Boogie-PL
//
//  Readme 
//  ws 5/9/03
// ----------------------------------------------------------------------------


This directory cointains the Boogie Procedural Language (BoogiePL) 
implementataion and "1" sample program.


Scanner and parser are generated with Coco (ann LL1 parser generator for EBNFs) 
(see http://www.ssw.uni-linz.ac.at/Research/Projects/Coco/CSharp/)

	The input file is
	  BoogiePL.atg
	then simply call 
	  ..\Coco\bin\Debug\Coco.exe BoogiePL.atg
	it then uses (as input)
	  Scanner.frame
	  Parser.frame
	as templates to generate an LL1 parser into
	  Scanner.cs
	  Parser.cs
	as output

The Csharp excutable then contains 

	BoogiePL.cs		-- main program
	Absy			-- abstract syntax for BoogiePL
	Error.cs		-- error handling (contains still some oldstuff)
	Parser.cs		-- generated parser		
	Scanner.cs		-- generated scanner
	PureCollections.cs	-- sets/maps/tuples/ (contains still some oldstuff)

The directory Samples contains one parsing example
	Parsing1.pl
Please check it for the syntax, alternatively consult BoogiePL.atg
	
Here is its output:
	C:\Boogie> bin\debug\Boogiepl.exe samples\Parsing1.pl
	
	Boogie Procedural Language Version 0.1 Copyright (c) Microsoft 2003
	Parsing samples\Parsing1.pl		<<<===  here is what is does
	0 errors detected

Things left to do:

	BoogiePL needs a tiny context analysis 
	  checking names, updates, arities, OLD, etc.	
	  					(ws will do until 5/8)
	  
	BoogiePL Absy might be too flexible 
	  simplify (if one things so..)		(Mike/Rustan will do)

	BoogiePL needs more examples/experiences
						(all of us..)



