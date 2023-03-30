(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

open Dolmen

module KindTerm = Term
module E = CmcErrors
module Ids = Lib.ReservedIds

(* Instantiate a module for parsing logic languages *)
module Loc = Std.Loc
module Id = Std.Id
module Term = Std.Term
module Statement = Std.Statement
module M = Class.Logic.Make(Loc)(Id)(Term)(Statement)
module DU = DolmenUtils

module I = LustreIdent

let (let*) = Res.(>>=)

type loc = Loc.t
type id = Id.t
type term = Term.t
type statement = Statement.t

type def = {name: id}

type subsystem_scope = string list
type sys_var_mapping = (subsystem_scope * StateVar.t list) list

type system_def = {
  name: id;
  input: (id * Type.t) list;
  output: (id * Type.t) list;
  local: (id * Type.t) list;
  init: term option;
  trans: term option;
  inv:  term option;

  (*          ( sys_name * ( local_name * inputs list) list ) list    *)
  subsystems: (id * (id * id list) list) list;
}

let match_sys_def sys_def v = 
  List.find ( fun {name; _ } -> Id.equal name v) sys_def 

type base_trans_system = {
  top: bool;
  name: id;
  (* sys_def: system_def; *) (* TODO may need to reintroduce if determined to be nessisary for cex printing *)
  input_svars: (Id.t * StateVar.t) list; (* TODO remove ID if not used *)
  output_svars: (Id.t * StateVar.t) list;
  local_svars: (Id.t * StateVar.t) list;
  init_map: (Id.t * Var.t) list;
  trans_map: (Id.t * Var.t) list;
  scope: string list;
  init_flag: StateVar.t;
  state_vars: StateVar.t list;
  init_uf_symbol: UfSymbol.t;
  init_formals: Var.t list;
  init_term: KindTerm.t;
  trans_uf_symbol: UfSymbol.t;
  trans_formals: Var.t list;
  trans_term: KindTerm.t;
  subsystems: (Id.t * TransSys.instance list) list;
  props: Property.t list;
}

type env = {
  base_trans_systems: ( Id.t * base_trans_system ) list;
  defined_functions: TransSys.d_fun list;
  declared_functions: UfSymbol.t list;
  global_constants: StateVar.t list;
}

let rec mk_subsys_structure sys = {
  SubSystem.scope = TransSys.scope_of_trans_sys sys;
  source = sys;
  has_contract = false;
  has_impl = true;
  has_modes = false;
  subsystems =
    TransSys.get_subsystems sys
    |> List.map mk_subsys_structure;
}

(* TODO: This is not yet populated
   Make sure that this is still the best method and implement if so
   Also define its purpose here*)
type subsystem_instance_name_data = {
  map: (Lib.position * HString.t) list;
  counter: int;
}

let empty_subsystem_instance_name_data = {
  map = [];
  counter = 0;
}

type enum = {
  name: HString.t;
  get_type: Type.t;
  to_int: (HString.t * Numeral.t) list;
  to_str: (Numeral.t * HString.t) list;
}

let empty_enum name enum_type = {
  name = name;
  get_type = enum_type;
  to_int = [];
  to_str = [];
}

type definitions = {
  system_defs: base_trans_system list;
  functions: TransSys.d_fun list; (* Not yet populated *)
  enums: enum list; (* Not yet populated *)
  ufunctions: UfSymbol.t list; (* Not yet populated *)
  name_map: subsystem_instance_name_data; (* Not yet populated *)
  (* TODO Others *)
}

let empty_definitions = {
  system_defs = [];
  functions = [];
  enums = [];
  ufunctions = [];
  name_map = empty_subsystem_instance_name_data;
}

(* TODO Remove position from error if it is never used *)
let error ?(pos=Lib.dummy_pos) e = Error (`CmcInterpreterError (pos, e))

let find_system definitions name =
  let systems = definitions.system_defs in
  List.find_opt (fun (system : base_trans_system) -> Id.equal system.name name) systems

let update_system (definitions : definitions) (updated_system : base_trans_system) = 
  (* Assumes that the system exists in the list *)
  let rec func (definitions : base_trans_system list) id c = match definitions with
  | [] -> raise(Failure "Not Found")
  | hd::tl -> if (Id.equal hd.name id) then c else func tl id (c+1) in
  let sys_index = func definitions.system_defs updated_system.name 0 in
  {definitions with 
  system_defs = List.mapi (fun i def -> if i = sys_index then updated_system else def) definitions.system_defs }

let mk_var sys_name is_input is_const (init_map, trans_map, svars) (id, var_type) = 
  (* TODO Verify (or likely correct) that defined vars have valid names *)
  let svar =
    let name = DU.dolmen_id_to_string id in
    let scope = (sys_name :: "impl" :: I.user_scope) in
    StateVar.mk_state_var
      ~is_input ~is_const ~for_inv_gen:true
      name scope var_type
    in
    Format.printf "%a\n" StateVar.pp_print_state_var_debug svar;
    let prev_base = Numeral.pred TransSys.trans_base in (* Why is this the previous value? ?*)
    let next_id = DU.prime id in
    let prev_mapping = (id, Var.mk_state_var_instance svar prev_base) in
    let next_mapping = (next_id, Var.mk_state_var_instance svar TransSys.trans_base) in
    (prev_mapping :: init_map, prev_mapping :: next_mapping :: trans_map, (id, svar) :: svars)

let mk_vars sys_name is_input mappings dolmen_terms = 
  let vars = List.map DU.dolmen_term_to_id_type (DU.opt_list_to_list dolmen_terms) in
  List.fold_left (mk_var sys_name is_input false) mappings vars

(** A mapping of unprimed vars to their primed state. 
    Specifically used for invariant props in the transition system. *)
let mk_inv_map init_map trans_map =  
  init_map |> List.map (fun (unprimed_var, _) -> 
    let primed_var = DU.prime unprimed_var in 
    (unprimed_var, List.assoc primed_var trans_map )
  ) 

(** Translate CMC init sexp into Kind2 Term. Ands init with the inv property *)
let mk_init_term ({ init; inv}: Statement.sys_def) init_flag const_map init_map inv_map =
  (* Flag representing the init state*)
  let init_flag_t =
      Var.mk_state_var_instance init_flag TransSys.init_base
      |> KindTerm.mk_var
  in

  KindTerm.mk_and (init_flag_t :: 
                   DU.opt_dolmen_term_to_expr (const_map @ init_map) init :: 
                   DU.opt_dolmen_term_to_expr (const_map @ inv_map) inv :: 
                   []
                  )

let mk_trans_term ({ trans; inv}: Statement.sys_def) init_flag const_map inv_map trans_map =
  (* Flag representing the init state*)
  let init_flag_t =
    Var.mk_state_var_instance init_flag TransSys.trans_base
    |> KindTerm.mk_var
  in

  (* TODO Reintroduce support for OnlyChange
     Refer old sexp interpreter. May want to add this in DolmelUtils and create a new ast type for this
     *)
  (* let trans = process_only_change sys_def trans in *)

  KindTerm.mk_and (KindTerm.mk_not init_flag_t :: DU.opt_dolmen_term_to_expr (const_map @ trans_map) trans :: DU.opt_dolmen_term_to_expr (const_map @ inv_map) inv :: [])



(** Process the CMC [define-system] command. *)
let mk_base_trans_system env (sys_def: Statement.sys_def) = 
  let system_name = DU.dolmen_id_to_string sys_def.id in
  let scope = [system_name] in
  let init_flag = StateVar.mk_init_flag scope in

  let init_map, trans_map, input_svars = mk_vars system_name true ([], [], []) sys_def.input in
  let init_map, trans_map, output_svars = mk_vars system_name true (init_map, trans_map, []) sys_def.output in
  let init_map, trans_map, local_svars = mk_vars system_name true (init_map, trans_map, []) sys_def.local in

  (* TODO May need to make this an assoc list as in the sexp interpreter *)
  let symb_svars = input_svars @ output_svars @ local_svars in (*S*)

  (* TODO Lots of subsystem stuff here *)
  
  (* let const_map = mk_init_map const_decls in *)
  let const_map = [] in (* TODO *)
  
  let inv_map_for_init = init_map in (* For notational puposes only. Just need the inv map for the init formula. *)
  let inv_map_for_trans = mk_inv_map init_map trans_map in
  
  (* TODO More subsystem stuff here. Refer to old sexp interpreter *)
  
  (* let subsystem_defs = mk_subsystems prev_trans_systems system_name cmc_sys_def.subsystems symb_svars in *)
  (* let named_subsystems = List.map fst subsystem_defs in  *)
  (* let subsystems, name_map = ... *) 
  (* TODO namemap should take the previous name map and add info to it 
    the previous namemap should be passed to this function (see sexp implementation) *)
  let subsystems, name_map = [], empty_subsystem_instance_name_data in
  (* let subsys_call_maps = List.map fst (List.map snd subsystem_defs) in *)
  (* let subsys_locals = List.flatten (List.map snd (List.map snd subsystem_defs)) in *)
  let subsys_locals = [] in
  (* let subsys_terms = ... *)
  (* let subsys_init = List.map fst subsys_terms in *)
  let subsys_init = [] in
  (* let subsys_trans = List.map snd subsys_terms in *)
  let subsys_trans = [] in

  let init_term = 
    KindTerm.mk_and ((mk_init_term sys_def init_flag const_map init_map inv_map_for_init) :: subsys_init )
  in
 
  let trans_term = 
    KindTerm.mk_and ((mk_trans_term sys_def init_flag const_map inv_map_for_trans trans_map) :: subsys_trans )
  in

  let state_vars =
    init_flag :: List.map snd (symb_svars @ subsys_locals)
   in

  let init_formals =  (* BOTH NEEDS SEPERATED *)
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in


  let init_uf_symbol = (* BOTH NEEDS SEPERATED *)
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.init_uf_string system_name)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  let trans_formals = (* BOTH NEEDS SEPERATED *)
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.trans_base
    )
    state_vars
    @
    List.map (fun sv ->
      Var.mk_state_var_instance
        sv (TransSys.trans_base |> Numeral.pred)
    )
    state_vars
  in
  
  let trans_uf_symbol =  (* BOTH NEEDS SEPERATED *)
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" Ids.trans_uf_string system_name)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in
  Format.printf "CMC_SYS: %s." (UfSymbol.name_of_uf_symbol trans_uf_symbol) ;

  (* TODO Determine what this is for and fix it ( Started earlier and forgot purpose ) *)
  let symb_svars = symb_svars @ subsys_locals  in 
  {top=false; scope; name=sys_def.id;  input_svars; output_svars; local_svars; init_map; trans_map; init_flag; state_vars; init_uf_symbol; init_formals; init_term; trans_uf_symbol; trans_formals; trans_term; subsystems; props=[]}, name_map

let rename_check_vars (sys_def : base_trans_system) (system_check : Statement.sys_check) = 
  (* Requires that the sys_def and check_def match *)
  (* TODO Support underscores *)
  assert (Id.equal sys_def.name system_check.id) ;
  let system_name = DU.dolmen_id_to_string sys_def.name in
  let init_map, trans_map, _ = mk_vars system_name true ([], [], []) system_check.input in
  let init_map, trans_map, _ = mk_vars system_name true (init_map, trans_map, []) system_check.output in
  let _, trans_map, _ = mk_vars system_name true (init_map, trans_map, []) system_check.local in

  List.map2 (fun map chk -> (fst chk,  snd map)) sys_def.trans_map trans_map  

(** Reachibility queries in terms of invariance *)
(* Simply states that the invariant variable must equal the formula. Makes no other claims *)
let mk_trans_invar_prop_eqs one_query_prop_svars (system_check : Statement.sys_check) two_state_bound_var_map =  
  one_query_prop_svars |> List.map (fun ((id: id), (svar: StateVar.t)) ->
    (* Typechecker should allow us to assume that the reachability prop is defined *)
    let prop = List.assoc id system_check.reachable in
    let prop = KindTerm.mk_not (DU.dolmen_term_to_expr two_state_bound_var_map prop) in
    let var = Var.mk_state_var_instance svar Numeral.zero in
      (KindTerm.mk_eq
        [KindTerm.mk_var var; prop])
    |> KindTerm.bump_state Numeral.one
  )

(* TODO Determine if/why this init version is needed *)
let mk_init_invar_prop_eqs one_query_prop_svars (system_check : Statement.sys_check) two_state_bound_var_map =  
  one_query_prop_svars |> List.map (fun ((id: id), (svar: StateVar.t)) ->
    (* Typechecker should allow us to assume that the reachability prop is defined *)
    let prop = List.assoc id system_check.reachable in
    let prop = KindTerm.mk_not (DU.dolmen_term_to_expr two_state_bound_var_map prop) in
    let var = Var.mk_state_var_instance svar TransSys.init_base in
      (KindTerm.mk_eq
        [KindTerm.mk_var var; prop])
  )

let mk_rprops (system_check : Statement.sys_check) two_state_bound_var_map = 
  let reachability_svars = system_check.reachable |> List.map (fun (prop_id, prop) ->
    let system_name = DU.dolmen_id_to_string system_check.id in
    let scope = (system_name :: I.reserved_scope) in

    let reachable_name = DU.dolmen_id_to_string prop_id in

    let svar = StateVar.mk_state_var
      ~is_input:false ~is_const:false ~for_inv_gen:true
      reachable_name scope Type.t_bool in

    (prop_id, svar)
  ) in
  let init_invar_props = mk_init_invar_prop_eqs reachability_svars system_check two_state_bound_var_map in
  let trans_invar_props = mk_trans_invar_prop_eqs reachability_svars system_check two_state_bound_var_map in
  (reachability_svars, init_invar_props, trans_invar_props)

let mk_query (rprop_svars : (id * StateVar.t) list) query =
  let query_id, query_body = query in

  let reachability_svars = List.map (fun reachability_prop -> 
    let prop_id = DU.dolmen_symbol_term_to_id reachability_prop in
    List.assoc prop_id rprop_svars) query_body in

  (* We or instead of and because the whole reachability query must be notted for invariance*)
  let mk_var_kind_term svar = KindTerm.mk_var (Var.mk_state_var_instance svar TransSys.prop_base) in
  (query_id, KindTerm.mk_or (List.map mk_var_kind_term reachability_svars);)

let check_trans_system base_system (system_check: Statement.sys_check) = 
  (* Map renamed check sys state vars (primed and unprimed) to actual system vars *)
  let check_map = rename_check_vars base_system system_check in

  (* Make svars, init terms, and trans terms for each reachability prop *)
  let reachability_svars, rprop_init_terms, rprop_trans_terms = mk_rprops system_check check_map in
  
  (* Create a statevar for each reachability prop within a query *)
  (* Other reachability props are ignored *)
  (* TODO only supports one query*)
  let queries = system_check.queries |> List.map (mk_query reachability_svars) in

  (* Placeholder for when assumption ,fairness, etc are added *)
  let prop_svars = List.map snd reachability_svars in

  (* TODO Determine if init term is needed. may have issues when primed vars are present *)
  let init_term = KindTerm.mk_and ( base_system.init_term :: rprop_init_terms ) in
  let trans_term = KindTerm.mk_and ( base_system.trans_term :: rprop_trans_terms ) in
  
  let props = (*C*)
     queries |> List.map (fun (query_id, query_term) ->
      {      

        Property.prop_name = DU.dolmen_id_to_string query_id; (*Used to prepend invar-property-*)
        prop_source = Property.PropAnnot Lib.dummy_pos;
        prop_term = query_term;
        prop_status = Property.PropUnknown
      }
    )
  in

  let state_vars =
    base_system.state_vars @ prop_svars
   in

  let init_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.init_base
    )
    state_vars
  in

  let init_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.asprintf "%s_%a_checked" Ids.init_uf_string Id.print system_check.id)  (*TODO need to change name to support multiple checks*)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  let trans_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TransSys.trans_base
    )
    state_vars
    @
    List.map (fun sv ->
      Var.mk_state_var_instance
        sv (TransSys.trans_base |> Numeral.pred)
    )
    state_vars
  in

  let trans_uf_symbol =
    (* TODO we are redeclaring uf symbol with updated type
       This is bad, to get around it we add checked to it. 
       We may need to postpone the initial declararion when checks are present if 
        we want to stop this *)
    UfSymbol.mk_uf_symbol
      (Format.asprintf "%s_%a_checked" Ids.trans_uf_string Id.print system_check.id)  (*TODO need to change name to support multiple checks*)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in

  {base_system with 
    init_term; trans_term; props;
    state_vars; 
    init_formals; init_uf_symbol;
    trans_formals; trans_uf_symbol}

let process_decl definitions (dec : Statement.decl) = 
  Format.printf "TODO process decl: %a\n" Statement.print_decl dec ;
  definitions

let process_def definitions (def : Statement.def) = 
  Format.printf "TODO process def: %a\n" Statement.print_def def ;
  definitions
  
let process_command definitions Statement.({id; descr; attrs; loc}) = 
  let* defs = definitions in
  match descr with
    (* (define-system symbol attrs)*)
  | Statement.Def_sys s -> 
    (* TODO update name_map instead of replaceing it *)
    let sys_def, name_map = mk_base_trans_system definitions s in

    Ok {defs with system_defs = sys_def :: defs.system_defs ; name_map;}
    
  | Statement.Chk_sys c ->
    (* Assuming check systems come after system definitions. 
       Changes will be needed if we want to remove this assumption. *)
    let* checked_system = 
      match find_system defs c.id with
       | Some system -> Ok (check_trans_system system c)
       | None -> (error (E.SystemNotFound c.id)) in

    Ok (update_system defs checked_system)

  
  (* (declare-fun name args type) *)
  | Statement.Decls fun_decls -> 
    Ok (List.fold_left process_decl defs fun_decls.contents)

  (* (define-fun name args type) *)
  | Statement.Defs fun_defs -> 
    Ok (List.fold_left process_def defs fun_defs.contents)

  | Statement.Set_logic l -> 
    (* TODO Actually do something here? *)
    Ok defs
  | _ -> (error (E.NotSuppoted (DU.dolmen_opt_id_to_string id)))

(* Open and parse from file *)
let of_file filename = 

  (* Parse and Typecheck file with Dolmen *)
  let format, _, statements = M.parse_file filename in
  let t = DU.process [] filename None in
  Format.printf "DONE" ;

  
  let* cmc_defs =
    List.fold_left process_command (Ok empty_definitions) statements
  in

  let cmc_sys_defs = cmc_defs.system_defs in
  Format.printf "LEN: %d@." (List.length cmc_sys_defs);

  (* TODO *)
  (* let enum_defs = cmc_defs.enums in *)
  let enum_defs = [] in
  (* We should no longer need to generate a sys ordering or
     determine cyclic system dependencies beacuse our typechecker verifys this.
     The typechecker requires that subsystems are defined before they are referenced.
     If we decide to remove this restriction, changes will need to be made
     to the typechecker and we will need to reintroduce the system ordering. *)

  (* TODO Match check_system commands with the system definitions and apply the props *)
  (* let cmc_check_defs = cmc_defs.system_checks in *)

  (* TODO create a mapping for systems to their vars like in the sexp interpreter. 
     This is required for counterexample printing. *)
  (* let sys_var_mapping = ...*)  
  let sys_var_mapping = [] in

  (* TODO implement after subsystems are used for CEX printing *)
  let name_map = cmc_defs.name_map in

  let mk_trans_system global_const_svars other_trans_systems (base : base_trans_system)  =
    let name = base.name in
    let subs = base.subsystems |> List.map (fun (name, local_instances) -> 
      (List.assoc name other_trans_systems, local_instances)) (* subsystems *)
    in
    let global_const_vars = List.map Var.mk_const_state_var global_const_svars in
    let sys, _ = 
      TransSys.mk_trans_sys
        base.scope
        None (* No instance variable *)
        base.init_flag
        base.state_vars
        StateVar.StateVarSet.empty (* underapproximation *)
        (StateVar.StateVarHashtbl.create 7) (* state_var_bounds *)
        global_const_vars (* global_consts *)
        (if base.top then cmc_defs.ufunctions else []) (* ufs *)
        (if base.top then cmc_defs.functions else []) (* defs *)
        base.init_uf_symbol
        base.init_formals
        base.init_term
        base.trans_uf_symbol
        base.trans_formals
        base.trans_term
        subs
        base.props
        (* fg_props *)
        (None, []) (* mode_requires *)
        (Invs.empty ()) (* invariants *)
    in
    (name, sys) :: other_trans_systems
  in

  (* TODO Add global vars to this list *)
  let const_global_vars = [] in (* List.map snd cmc_defs.const_decls in *)
  let trans_systems = cmc_sys_defs |> List.fold_left (mk_trans_system const_global_vars) [] in
  
  let top_sys = snd (List.hd trans_systems) in

    (* NOTE: This was originaly commented out *)
  Format.printf "CMC_SYS: %a@." (TransSys.pp_print_subsystems true) top_sys;

  (* TODO pass all extra params for cex printing *)
  Ok (mk_subsys_structure top_sys, name_map, sys_var_mapping, enum_defs)
  (* Ok (mk_subsys_structure top_sys) *)

  (* (error (E.Impossible "CMC Interpreter with Dolmen not finished!")) *)

