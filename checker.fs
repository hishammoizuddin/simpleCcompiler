//
// Analyzer for simple C programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input
// program is legal, otherwise the string "type_error: ..."
// is returned denoting an invalid simple C program.
//
// Modified by:
//   Mohammed Hisham Moizuddin
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module checker =
  //
  // NOTE: all functions in the module must be indented.
  //

  let rec c_check rem symbT =
    match symbT with
    | [] -> (false, "")
    | (name, nType)::tl when name = rem -> (true, nType)
    | hd::tl -> c_check rem tl
  
  let c_checkFT rem symbT =
    let nameN = List.filter(fun(name, nType) -> name = rem) symbT
    if nameN.Length > 0 then
      true
    else
      false

  let private matchToken expected_token (tokens: string list) =
    //
    // if the next token matches the expected token,
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a
    // syntax error, effectively stopping compilation:
    //
    // NOTE: identifier, int_literal and str_literal
    // are special cases because they are followed by
    // the name or literal value. In these cases exact
    // matching will not work, so we match the start
    // of the token in these cases.
    //
    let next_token = List.head tokens

    if expected_token = "identifier" && next_token.StartsWith("identifier") then
      //
      // next_token starts with identifier, so we have a match:
      //
      List.tail tokens
    elif expected_token = "int_literal" && next_token.StartsWith("int_literal") then
      //
      // next_token starts with int_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "str_literal" && next_token.StartsWith("str_literal") then
      //
      // next_token starts with str_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "real_literal" && next_token.StartsWith("real_literal") then
      List.tail tokens // next token starts with real_literal
    
    elif expected_token = next_token then
      List.tail tokens
    else
      failwith ("expecting " + expected_token + ", but found " + next_token)

  //
  // <expr-value> -> identifier
  //               | int_literal
  //               | str_literal
  //               | true
  //               | false
  //
  let rec private expr_value tokens symbT =
    let next_token = List.head tokens
    //
    if next_token = "false" then
      let T2 = matchToken "false" tokens
      (T2,"bool")
    elif next_token = "true" then
      let T2 = matchToken "true" tokens
      (T2,"bool")
    //
    // the others are trickier since we have to look
    // at the start of the string for a match:
    //
    elif next_token.StartsWith("identifier") then
      let rem = next_token.[11..]
      if (c_checkFT rem symbT) then
        let T2 = matchToken "identifier" tokens
        let (name, nType) = c_check rem symbT
        (T2, nType)
      else
        failwith ("variable '" + rem + "' undefined")
    elif next_token.StartsWith("int_literal") then
      let T2 = matchToken "int_literal" tokens
      (T2, "int")
    elif next_token.StartsWith("str_literal") then
      let T2 = matchToken "str_literal" tokens
      (T2, "str")
    elif next_token.StartsWith("real_literal") then
      let T2 = matchToken "real_literal" tokens
      (T2, "real")
    else
      failwith ("expecting identifier or literal, but found " + next_token)

  //
  // <expr-op> -> +
  //            | -
  //            | *
  //            | /
  //            | ^
  //            | <
  //            | <=
  //            | >
  //            | >=
  //            | ==
  //            | !=
  //
  let rec private expr_op tokens =
    let next_token = List.head tokens

    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then

      let T2 = matchToken next_token tokens
      (T2, next_token)
    else
      failwith ("expecting expression operator, but found " + next_token)
      
  //
  // <expr> -> <expr-value> <expr-op> <expr-value>
  //         | <expr-value>
  //
  
  let rec private expr tokens symbT =
    //
    // first we have to match expr-value, since both
    // rules start with this:
    //
    let (T2, aType) = expr_value tokens symbT
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head T2

    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then

      let (T3, oper) = expr_op T2
      let (T4, bType) = expr_value T3 symbT
      
      if oper = "+" || oper = "-" || oper = "*" || oper = "/" || oper = "^" then
        if (aType = "real" || aType = "int") && aType = bType then
          (T4, aType)
        else
          failwith ("operator " + oper + " must involve 'int' or 'real'")
      else
        if oper = "==" && (aType = "real" || bType = "real") then
          printfn "warning: comparing real numbers with == may never be true"
          (T4, "bool")
        elif aType = bType then
          (T4, "bool")
        else
          failwith ("type mismatch '" + aType + "' " + oper + " '" + bType + "'")
    else
      (T2, aType)


  //
  // <empty> -> ;
  //
  let rec private empty tokens =
    let T2 = matchToken ";" tokens
    T2

  //
  // <vardecl> -> int identifier ;
  //
  let rec private vardecl tokens =
    if (List.head tokens) = "real" then
      let T2 = matchToken "real" tokens
      let T3 = matchToken "identifier" T2
      let T4 = matchToken ";" T3
      T4
    else
      let T2 = matchToken "int" tokens
      let T3 = matchToken "identifier" T2
      let T4 = matchToken ";" T3
      T4

  //
  // <input> -> cin >> identifier ;
  //
  let rec private input tokens symbT =
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2
    let T3_head = List.head T3
    let rem = T3_head.[11..]
    if (c_checkFT rem symbT) then
      let T4 = matchToken "identifier" T3
      let T5 = matchToken ";" T4
      T5
    else
      failwith ("variable '" + rem + "' undefined")


  //
  // <output-value> -> <expr-value>
  //                 | endl
  //
  let rec private output_value tokens symbT =
    let next_token = List.head tokens
    if next_token = "endl" then
      let T2 = matchToken "endl" tokens
      T2
    else
      let (T2, nType) = expr_value tokens symbT
      T2

  //
  // <output> -> cout << <output-value> ;
  //
  let rec private output tokens symbT =
    let T2 = matchToken "cout" tokens
    let T3 = matchToken "<<" T2
    let T4 = output_value T3 symbT
    let T5 = matchToken ";" T4
    T5

  //
  // <assignment> -> identifier = <expr> ;
  //
  //
  let rec private assignment (tokens: string list) symbT =
    let token_head = List.head tokens
    let rem = token_head.[11..]
    let (name, aType) = c_check rem symbT
    if name = true then
      let T2 = matchToken "identifier" tokens
      let T3 = matchToken "=" T2
      let (T4, bType) = expr T3 symbT
      if (aType = "real" && bType.StartsWith("int") || bType.StartsWith(aType)) then
        let T5 = matchToken ";" T4
        T5
      else
        let cType =
          if bType.StartsWith("int") then
            "int"
          elif bType.StartsWith("str") then
            "str"
          elif bType.StartsWith("real") then
            "real"
          else "bool"
        failwith ("cannot assign '" + cType + "' to variable of type '" + aType + "'")
    else
        failwith ("variable '" + rem + "' undefined")

  //
  // <stmt> -> <empty>
  //         | <vardecl>
  //         | <input>
  //         | <output>
  //         | <assignment>
  //         | <ifstmt>
  //
  let rec private stmt tokens symbT =
    let next_token = List.head tokens
    //
    // use the next token to determine which rule
    // to call; if none match then it's a syntax
    // error:
    //
    if next_token = ";" then
      let T2 = empty tokens
      T2
    elif next_token = "int" then
      let T2 = vardecl tokens
      T2
    elif next_token = "cin" then
      let T2 = input tokens symbT
      T2
    elif next_token = "cout" then
      let T2 = output tokens symbT
      T2
    elif next_token.StartsWith("identifier") then
      let T2 = assignment tokens symbT
      T2
    elif next_token = "if" then
      let T2 = ifstmt tokens symbT
      T2
    elif next_token = "real" then
      let T2 = vardecl tokens
      T2
    else
      failwith ("expecting statement, but found " + next_token)
  //
  // <ifstmt> -> if ( <condition> ) <then-part> <else-part>
  //
  and private ifstmt tokens symbT =
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let T4 = condition T3 symbT
    let T5 = matchToken ")" T4
    let T6 = then_part T5 symbT
    let T7 = else_part T6 symbT
    T7
  //
  // <condition> -> <expr>
  //
  and private condition tokens symbT =
    let (T2, nType) = expr tokens symbT
    if nType = "bool" then
      T2
    else
      failwith ("if condition must be 'bool', but found '" + nType + "'")
  //
  // <then-part> -> <stmt>
  //
  and private then_part tokens symbT =
    let T2 = stmt tokens symbT
    T2
  //
  // <else-part> -> else <stmt>
  //              | EMPTY
  //
  and private else_part tokens symbT =
    let next_token = List.head tokens
    if next_token = "else" then
      let T2 = matchToken "else" tokens
      let T3 = stmt T2 symbT
      T3
    else
      // EMPTY, do nothing but return tokens back
      tokens


  //
  // <morestmts> -> <stmt> <morestmts>
  //              | EMPTY
  //
  let rec private morestmts tokens symbT =
    //
    // if the next token denotes the start of a stmt
    // then process stmt and morestmts, otherwise apply
    // EMPTY
    //
    let next_token = List.head tokens

    if next_token = ";"    ||
       next_token = "int"  ||
       next_token = "real" ||
       next_token = "cin"  ||
       next_token = "cout" ||
       next_token.StartsWith("identifier") ||
       next_token = "if" then

      let T2 = stmt tokens symbT
      let T3 = morestmts T2 symbT
      T3
    else
      // EMPTY => do nothing, just return tokens back
      tokens


  //
  // <stmts> -> <stmt> <morestmts>
  //
  let rec private stmts tokens symbT =
    let T2  = stmt tokens symbT
    let T3 = morestmts T2 symbT
    T3


  //
  // <simpleC> -> void main ( ) { <stmts> } $
  //
  let private simpleC tokens symbT =
    let T2 = matchToken "void" tokens
    let T3 = matchToken "main" T2
    let T4 = matchToken "(" T3
    let T5 = matchToken ")" T4
    let T6 = matchToken "{" T5
    let T7 = stmts T6 symbT
    let T8 = matchToken "}" T7
    let T9 = matchToken "$" T8  // $ => EOF, there should be no more tokens
    T9


  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
  let typecheck tokens symboltable =
    try
      let T2 = simpleC tokens symboltable
      "success"
    with
      | ex -> "type_error: " + ex.Message
