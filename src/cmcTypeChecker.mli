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

type error_kind = Unknown of string
| Impossible of string
| UnboundIdentifier of HString.t
| UnknownFunction of HString.t
| UnknownAttribute of HString.t * HString.t
| UnnamedAttribute of HString.t
| InvalidCommandSyntax of string


type cmc_type = 
   | Bool 
   | TBool 
   | SystemDef of cmc_type list * cmc_type list * cmc_type list (* inputs * outputs * locals *)

val error_message : error_kind -> string

val type_check : HStringSExprPos.t list ->
   ((HString.t * cmc_type) list,
    [> `CmcTypeCheckerError of Lib.position * error_kind ])
   result
