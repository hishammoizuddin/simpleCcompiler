//
// F# program to compile simple C programs. This is the main
// function denoting the compiler, calling the lexer, 
// parser, analyzer, etc.
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//


//##################################################################
//
// main
//
// Compiles the simple C program; the filename is input by the user.
//
[<EntryPoint>]
let main argv =
  //
  printf "simpleC filename> "
  let filename = System.Console.ReadLine()
  printfn ""
  //
  if not (System.IO.File.Exists(filename)) then
    printfn "**Error: file '%s' does not exist." filename
    0
  else
    printfn "compiling %s..." filename
    //
    // Run the lexer to get the tokens, and then
    // pass these tokens to the parser to see if
    // the input program is legal:
    //
    let tokens = compiler.lexer.analyze filename
    //
    printfn ""
    printfn "%A" tokens
    printfn ""
    //
    printfn "parsing %s..." filename
    let result = compiler.parser.parse tokens
    printfn "%s" result
    printfn ""
    //
    if result <> "success" then
      exit(0)
    //
    // no syntax errors, perform analysis
    //
    printfn "analyzing %s..." filename
    let (result, symboltable) = compiler.analyzer.build_symboltable tokens
    printfn "%s" result
    printfn ""
    //
    if result <> "success" then
      exit(0)
    //
    // symbol table built, now type-checking...
    //
    printfn "symbol table: %A" symboltable
    printfn ""
    //
    printfn "type-checking %s..." filename
    let result = compiler.checker.typecheck tokens symboltable
    printfn "%s" result
    printfn ""
    //
    0
