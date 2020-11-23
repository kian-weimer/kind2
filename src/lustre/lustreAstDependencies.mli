(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** Graph analysis on Lustre Ast Declarations.
  
    We build a dependency graph of the lustre declarations
    to detect circular dependencies and reject them. We also
    reorder node and contract declarations to resolve
    forward references and backend cannot handle them.

    Note {!Types of dependency analysis}: There are three different kinds of 
    graph dependency analysis and sorting done here. 

    1. Top level constants and type declarations and functions (starts at [mk_graph_decls]) 

    2. Nodes and contracts (starts at [mk_graph_decls])

    3. Sorting equations of contracts and cirular analysis of node equations 

   TODO: This should module should supercede LustreDependencies when it hardens.     

   @author Apoorv Ingle *)

module LA = LustreAst
          
type 'a graph_result = ('a, Lib.position * string) result
(** Result of the dependency analysis *)
                       
val sort_and_check_declarations: LA.t -> LA.t graph_result
(** Returns a topological order of declarations, it also reorders contract equations
    and makes sure that node equations are not circular. 
 *)
