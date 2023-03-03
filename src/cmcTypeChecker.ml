(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib

module R = Res
module D = GenericSMTLIBDriver
module HS = HStringSExpr
module HSP = HStringSExprPos

let conv = D.smtlib_string_sexpr_conv
let conv_type_of_sexpr = conv.D.type_of_sexpr

type error_kind = Unknown of string
| Impossible of string
| UnboundIdentifier of HString.t
| UnknownFunction of HString.t
| UnknownAttribute of HString.t * HString.t
| UnnamedAttribute of HString.t
| InvalidCommandSyntax of string
(* Add more as needed*)

type error = [
  | `CmcTypeCheckerError of Lib.position * error_kind
]

let soh = HString.string_of_hstring

let error_message kind = match kind with
  | Unknown s -> s
  | Impossible s -> "This should be impossible! " ^ s
  | UnboundIdentifier id -> "Unbound identifier: " ^ soh id
  | UnknownFunction id -> "Unknown Function Call: " ^ soh id
  | UnknownAttribute (attr_id, fun_id) -> "Unknown attribute " ^ soh attr_id ^ "used in function call " ^ soh fun_id 
  | UnnamedAttribute fun_id -> "Attribute value passed without name in function call " ^ soh fun_id 
  | InvalidCommandSyntax info -> info
  (* Add more as needed*)

let (>>=) = R.(>>=)
let (let*) = R.(>>=)
let (>>) = R.(>>)

let type_error pos kind = Error (`CmcTypeCheckerError (pos, kind))
(** [type_error] returns an [Error] of [tc_result] *)

type cmc_type = 
   | Bool 
   | TBool 
   | SystemDef of cmc_type list * cmc_type list * cmc_type list (* inputs * outputs * locals *)

let declare_const = "declare-const"
let define_system = "define_system"

let get_basic_type hs = match soh hs with
   | "Bool" -> Some TBool
   | _ -> None

let type_check_atom env (a : HSP.atom) = 
   let pos, value = a.pos, a.value in
   match List.assoc_opt value env with
   | Some ty -> Ok (env, ty)
   | None ->
      match get_basic_type value with 
      | Some ty -> Ok (env, ty)
      | None -> 
         try 
            let ty = conv_type_of_sexpr (HS.Atom value) in
            (* TODO: Make sure type is valid for our SMT theory *)
            let is_core_theory = true in

            if is_core_theory then
               if Type.equal_types ty Type.t_bool then
                  Ok (env, Bool)
               else
                  type_error pos ( Impossible "The parser shouldn't allow this!" ) (* but it does... *)
            else
               type_error pos ( Impossible "The parser shouldn't allow this!" ) (* but it does... *)
         with Invalid_argument _ -> type_error pos ( UnboundIdentifier value )
         
let rec type_check_system_inputs env (input_cmd : HSP.atom) inputs = 
   match inputs with
   | HSP.List (HSP.Atom name :: HSP.Atom ty :: []) -> type_error Lib.dummy_pos (Impossible "TODO: Not implemented")
   | _ -> type_error input_cmd.pos (InvalidCommandSyntax "Invalid syntax used for input specification")

let rec type_check_define_system' env (sys_name : HSP.atom) args = 
   match args with 
   | HSP.Atom input_attr :: HSP.List inputs :: others when soh input_attr.value ==":input" ->
      type_error Lib.dummy_pos ( Impossible "not yet supported" )
   | HSP.Atom invalid_attr :: _ -> 
      (type_error sys_name.pos (UnknownAttribute (invalid_attr.value, sys_name.value)))
   | HSP.List _ :: _ -> type_error sys_name.pos (UnnamedAttribute sys_name.value)
   | [] -> (* TODO: Build up the function type now that all args have been processed. *)
      type_error Lib.dummy_pos ( Impossible "not yet supported" )
   
   


let type_check_define_system env args = 
   match args with 
   | HSP.Atom sys_name :: other -> type_error Lib.dummy_pos (Impossible "TODO: Not implemented")
      (* TODO: Ensure command name is a valid identifier *)
   | _ -> type_error Lib.dummy_pos (Impossible "TODO: Not implemented")
   

let type_check_function_call env (cmd: HSP.atom) args =
   match soh cmd.value with 
   | cmd when cmd == define_system -> type_check_define_system env args
   | _ -> type_error cmd.pos (UnknownFunction cmd.value)

let rec type_check_list env l = 
   match l with
   | [] -> type_error Lib.dummy_pos ( Impossible "The parser shouldn't allow this!" ) (* but it does... *)

   | HSP.Atom a :: [] -> type_check_atom env a
   | HSP.List l :: [] -> type_check_list env l
   (* Assume every sexp list with > 1 argument is a function call *)
   | HSP.Atom cmd :: args -> type_check_function_call env cmd args

   | HSP.List l :: args -> type_error Lib.dummy_pos ( Impossible "The parser shouldn't allow this!" ) (* but it does... *)

let type_check_sexpr env  (fc : HSP.t) = match fc with 
   | HSP.List l -> type_check_list env l
   | HSP.Atom a ->  type_check_atom env a

let rec type_check' env (sexps : HSP.t list) = 
   match sexps with 
   | [] -> Ok []
   | sexp :: [] -> 
      (* We dont care about the type at this level *)
      let* env', _ = type_check_sexpr env sexp in
      Ok env'
   | sexp :: sexps ->
      (* We dont care about the type at this level *)
      let* env', _ = type_check_sexpr env sexp in
      type_check' env' sexps   

let type_check sexps = 
   type_check' [] sexps
