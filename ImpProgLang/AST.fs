// Michael R. Hansen 03-01-2014
module AST
open System

type Exp = | Int of int 
           | Bool of bool 
           | String of string 
           | Var of string 
           | ContOf of Exp 
           | Apply of string * List<Exp>
           | Length of string
           | ArrayExp of string * Exp

and  Stm = | Asg of Exp * Exp
           | PrintLn of Exp
           | PrintStm of Stm
           | Seq of List<Stm>
           | While of Exp * Stm
           | Block of List<Dec> * Stm
           | Call of string * List<Exp>
           | Return of Exp
           | If of Exp * Stm * Stm
           | If1 of Exp * Stm
           | Read of Exp
           | Write of List<Exp>

and Dec  = | VarDec of string * Exp
           | ProcDec of string * List<string> * Stm
           | RecDec of Dec
           | ArrayDec of string * Exp * Exp


