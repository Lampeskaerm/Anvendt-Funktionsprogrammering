﻿(* Interpreter for a simple WHILE-language. Michael R. Hansen 03-01-2014 *)
(* Based on a natural semantics of WHILE                                 *)

(* Remember to regenerate the parser and the lexer using the commands 
   in README.txt if you modified the parser and lexer                    *)

module Interpreter 

open System
open AST
open System.IO

type Location = int
type Value    = | IntVal of int 
                | BoolVal of bool 
                | StringVal of string 
                | Reference of Location 
                | Primitive of (List<Value> -> Value)

and Env       = Map<string,Value>


type Closure =  List<string> * Env * Stm

type Content = SimpVal of Value | Proc of Closure |  ArrayCnt of Value [];;

type Store  = Map<Location,Content>  
  
let closureOf(ps,st) env = (ps, env, st)

// nextLoc() generates the next available location
let nextLoc: unit -> int =  let n = ref 0
                            let f x = (n := !n+1; !n)
                            f

    
    //Map.add y (Map.find x e) (addToEnv xs ys e);;

// exp: Exp -> Env -> Store -> Value * Store 
let rec exp e (env:Env) (store:Store) = 
    match e with
    | Var v       -> match Map.find v env with
                     | Reference loc as refl -> (refl,store)
                     | IntVal i              -> printfn "%s" (string i) ; failwith "errorXXX"
                     | _                     -> failwith "errorYYY"
    | ContOf er    -> match exp er env store with
                      | (Reference loc,store1) -> match Map.find loc store1 with 
                                                  | SimpVal res -> (res,store1)
                                                  | _           -> failwith "error"
                      | _                   -> failwith "error"

    | Apply(f,es) -> let (vals, store1) = expList es env store
                     match Map.find f env with 
                     | Primitive f   -> (f vals, store1) 
                     | Reference r   -> match (stm (Call (f,es)) env store) with
                                        | (Some x,s) -> (x,s)
                                        | _ -> failwith "true"
                     | _              -> failwith "type error"          
                                                               
    | Int i       -> (IntVal i, store)
    | Bool b      -> (BoolVal b,store)
    | String s    -> (StringVal s,store)
    | Length a    -> match Map.tryFind a env with
                     | None -> failwith "Array isn't initialised"
                     | Some (Reference loc) -> match Map.tryFind loc store with
                                               | None -> failwith "Location of array isn't in store"
                                               | Some (ArrayCnt arr) -> (IntVal arr.Length, store)
                                               | _ -> failwith "What you are searching for is not an array"
                     | _ -> failwith "Not returning a location"
    | ArrayExp(name, pos) -> let p = match (exp pos env store) with
                                     | (IntVal v,s) -> v
                                     | _ -> failwith "position in is not an integer"
                             match Map.tryFind name env with
                             | None -> failwith "Array isn't initialised"
                             | Some (Reference loc) -> match Map.tryFind loc store with
                                                       | None -> failwith "Location of array isn't in store"
                                                       | Some (ArrayCnt arr) -> (arr.[p], store)
                                                       | _ -> failwith "What you are searching for is not an array"
                             | _ -> failwith "Not returning a location"

and expList es env store = 
    match es with 
    | []       -> ([],store)
    | e::erest -> let (res1, store1) = exp e env store
                  let (ress, store2) = expList erest env store1
                  (res1::ress, store2)  

 
// stm: Stm -> Env -> Store -> option<Value> * Store
and stm st (env:Env) (store:Store) = 
    match st with 
    | Asg(el,e) -> match el with
                   | ArrayExp(n,p) -> let value = match (exp e env store) with
                                                  | (v,s) -> v
                                      let pos = match (exp p env store) with
                                                | (IntVal v,s) -> v
                                                | _ -> failwith "Position is not an integer"
                                      match Map.tryFind n env with
                                      | None -> failwith "Array isn't initialised"
                                      | Some (Reference loc) -> match Map.tryFind loc store with
                                                                | None -> failwith "Location of array isn't in store"
                                                                | Some (ArrayCnt arr) -> arr.[pos] <- value
                                                                                         (None, store)
                                                                | _ -> failwith "What you are searching for is not an array"
                                      | _ -> failwith "Not returning a location"
                   | _ ->  let (res,store1) = exp e env store
                           let (resl, store2) = exp el env store1
                           match resl with 
                           | Reference loc -> (None, Map.add loc (SimpVal res) store2) 
                           | _                               -> failwith "type error"
                   
                   
         
    | PrintLn e -> match exp e env store with
                   | (StringVal s,store1) -> (printfn "%s" s; (None,store1))
                   | _                    -> failwith "error"                  
    | PrintStm s -> match s with
                    | Read(_) -> match stm s env store with
                                 | (Some (StringVal st),_) -> (printfn "%s" st; (None,store))
                                 | _ -> failwith "Not returning a string"
                                 
                    | _ -> failwith "this function is for filereading/writing only"
                                           
    | Seq []        -> (None,store)
    | Seq (st::sts) -> match stm st env store with 
                       | (None,store1)   -> stm (Seq sts) env store1
                       | result       -> result

    | While(e,st1)  -> let (res, store1) = exp e env store
                       match res with 
                       | BoolVal true  -> match stm st1 env store1 with
                                          | (None,store2) -> stm st env store2
                                          | result     -> result
                       | BoolVal false -> (None, store1)
                       | _             -> failwith "type error"                     
 
    | Block(ds,st1) -> let (env1,store1) = decList ds env store 
                       stm st1 env1 store1 
    | Call(s,l) ->  match Map.tryFind s env with //Finds location of procedure in env
                    | None -> failwith "Procedure not existing"
                    | Some (Reference loc) ->   match Map.tryFind loc store with //Finds procedure in store
                                                | None -> failwith "Epic fail"
                                                | Some (Proc(l1, env1, stm1)) -> stm stm1 (addToEnv l l1 env store) store
                                                | _ -> failwith ("You are calling something that is not a function. Idiot.")
                    | _ -> failwith "Something wrong"
    | Return(x) -> match (exp x env store) with
                   | (v, s) -> (Some v, s)
    | If(e, stt, ste) -> match (exp e env store) with
                         | (BoolVal b, _) when b -> stm stt env store 
                         | (BoolVal b, _) -> stm ste env store
                         | _ -> failwith "Not a legal expression"
    | If1(e, st) -> match (exp e env store) with
                    | (BoolVal b, _) when b -> stm st env store
                    | (BoolVal b, _) -> (None, store)
                    | _ -> failwith "Not a legal expression"
    | Read(file) -> match exp file env store with
                    | (StringVal s, _) -> if File.Exists(s)
                                          then (Some(StringVal (File.ReadAllText(s))),store)
                                          else failwith "File doesn't exist"
                    | _ -> failwith "Filename is not a string"
    | Write(l) -> match l with
                  | [file;content] ->   match exp file env store with
                                        | (StringVal f, _) -> match exp content env store with
                                                              | (StringVal c,_) -> File.WriteAllText(f,c)
                                                                                   (None,store)
                                                              | _ -> failwith "The content you are trying to write to the file is not a string."
                                        | _ -> failwith "The filename is not a string"
                  | _ -> failwith "2 parameters is needed. (filename, content)"
                     
    
and decList ds env store = 
    match ds with
    | []       -> (env,store)
    | d::drest -> let (env1,store1) = dec d env store
                  decList drest env1 store1
//dec: Dec -> Env -> Store -> Env*Store
and dec d env store =
    match d with 
    | VarDec(s,e) -> let loc = nextLoc()
                     match exp e env store with
                     | (IntVal _ as res, store1)  
                     | (BoolVal _ as res, store1) 
                     | (StringVal _ as res, store1)  
                                                 -> let env2 = Map.add s (Reference loc) env
                                                    let store2 = Map.add loc (SimpVal res) store1
                                                    (env2, store2)
                     | _                         -> failwith "error"                                    
    | ProcDec(s, l, stm) -> let loc = nextLoc()
                            let env2 = Map.add s (Reference loc) env
                            let closure = (l, env2, stm)
                            let store2 = Map.add loc (Proc closure) store
                            (env2, store2)
    | RecDec(p) -> match p with
                   | ProcDec(_) -> dec p env store
                   | _ -> failwith "You are trying to run something recursively that is not a function"
    | ArrayDec(name, size, value) ->   let loc = nextLoc()
                                       match exp value env store with
                                       | (IntVal _ as res, store1)
                                       | (BoolVal _ as res, store1)
                                       | (StringVal _ as res, store1)
                                                                    ->  let env2 = Map.add name (Reference loc) env
                                                                        match exp size env store with
                                                                        | (IntVal s, _) -> 
                                                                                            let array = Array.init s (fun acc -> res)
                                                                                            let store2 = Map.add loc (ArrayCnt array) store1
                                                                                            (env2, store2)
                                                                        | _ -> failwith "Size of array is not an integer."
                                       | _ -> failwith "Values in array neither int, bool nor string"


// Adds variables to an environment
// addToEnv: List<Exp> -> List<string> -> Env -> Store -> Env
and addToEnv xs ys e store = 
    match (xs,ys) with
    | ([],[]) -> e
    | (_,[]) | ([],_) -> failwith "Not the correct number of parameters"
    | (x::xs, y::ys) -> match (exp x e store) with
                        | (v,s) -> Map.add y v (addToEnv xs ys e store);;

