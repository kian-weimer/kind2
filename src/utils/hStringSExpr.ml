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

(* Signature of an string atom as input for the functor {!SExprBase.Make} *)
module HStringAtom = struct 
  type t = HString.t 
  let pp_print_atom = HString.pp_print_hstring
end


(* Define the type of the result from the functor application *)
module type HStringSExpr = SExprBase.S with type atom = HString.t


(* Create a module of string S-expressions *)
module HStringSExpr = SExprBase.Make (HStringAtom)


(* Include the module here to avoid having to write
   HStringSExpr.HStringSExpr *)
include HStringSExpr


let rec equal s1 s2 = match s1, s2 with
  | Atom a1, Atom a2 -> a1 == a2
  | List l1, List l2 ->
    begin
      try List.for_all2 equal l1 l2
      with Invalid_argument _ -> false
    end
  | _ -> false


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
