(** Exact noninterference checks around the existing native mapper.

    Values' ordinary equality intentionally ignores several metadata fields for
    fixed-point convergence. It is therefore insufficient to justify reusing an
    old continuation after a selected loan update. Pair ordinary equality with
    an ordered inventory of the opaque metadata carriers in Values. Physical identity
    of each carrier preserves its complete original contents, including captured
    environments, without interpreting captures as current permissions.

    This module never restores or changes a value. Its callers may retain the
    original object only after the corresponding comparison succeeds. *)
open Values

type opaque_payload =
  | CapturedEnv of menv
  | MetaValue of mvalue
  | MetaSymbolic of msymbolic_value
  | ConsumedSymbolic of mconsumed_symb
  | GivenBackSymbolic of mgiven_back_symb
  | EndedProjectionBorrow of ended_proj_borrow_meta
  | EndedAbstractMutBorrow of aended_mut_borrow_meta
  | EndedExpressionMutBorrow of eended_mut_borrow_meta

let same_payload left right =
  match (left, right) with
  | CapturedEnv left, CapturedEnv right -> left == right
  | MetaValue left, MetaValue right -> left == right
  | MetaSymbolic left, MetaSymbolic right -> left == right
  | ConsumedSymbolic left, ConsumedSymbolic right -> left == right
  | GivenBackSymbolic left, GivenBackSymbolic right -> left == right
  | EndedProjectionBorrow left, EndedProjectionBorrow right -> left == right
  | EndedAbstractMutBorrow left, EndedAbstractMutBorrow right -> left == right
  | EndedExpressionMutBorrow left, EndedExpressionMutBorrow right -> left == right
  | _ -> false

let rec same_payloads left right =
  match (left, right) with
  | [], [] -> true
  | left :: lefts, right :: rights ->
      same_payload left right && same_payloads lefts rights
  | _ -> false

class collect_opaque (payloads : opaque_payload list ref) =
  object
    inherit [_] iter_env

    method! visit_menv () value =
      payloads := CapturedEnv value :: !payloads

    method! visit_mvalue () value =
      payloads := MetaValue value :: !payloads

    method! visit_msymbolic_value () value =
      payloads := MetaSymbolic value :: !payloads

    method! visit_mconsumed_symb () value =
      payloads := ConsumedSymbolic value :: !payloads

    method! visit_mgiven_back_symb () value =
      payloads := GivenBackSymbolic value :: !payloads

    (* These compound metadata records are separate opaque visitor leaves.
       The base visitor does not recurse into their given_back fields. *)
    method! visit_ended_proj_borrow_meta () value =
      payloads := EndedProjectionBorrow value :: !payloads

    method! visit_aended_mut_borrow_meta () value =
      payloads := EndedAbstractMutBorrow value :: !payloads

    method! visit_eended_mut_borrow_meta () value =
      payloads := EndedExpressionMutBorrow value :: !payloads
  end

let opaque_cont (cont : abs_cont option) : opaque_payload list =
  let payloads = ref [] in
  let visitor = new collect_opaque payloads in
  Option.iter (visitor#visit_abs_cont ()) cont;
  List.rev !payloads

let opaque_tavalue (value : tavalue) : opaque_payload list =
  let payloads = ref [] in
  (new collect_opaque payloads)#visit_tavalue () value;
  List.rev !payloads

let opaque_env_elem (value : env_elem) : opaque_payload list =
  let payloads = ref [] in
  (new collect_opaque payloads)#visit_env_elem () value;
  List.rev !payloads

let same_cont (left : abs_cont option) (right : abs_cont option) : bool =
  let ordinary_equal =
    match (left, right) with
    | None, None -> true
    | Some left, Some right -> equal_abs_cont left right
    | _ -> false
  in
  ordinary_equal && same_payloads (opaque_cont left) (opaque_cont right)

let same_tavalue (left : tavalue) (right : tavalue) : bool =
  equal_tavalue left right
  && same_payloads (opaque_tavalue left) (opaque_tavalue right)

let same_env_elem (left : env_elem) (right : env_elem) : bool =
  equal_env_elem left right
  && same_payloads (opaque_env_elem left) (opaque_env_elem right)

let rec same_env (left : env) (right : env) : bool =
  match (left, right) with
  | [], [] -> true
  | left :: lefts, right :: rights ->
      same_env_elem left right && same_env lefts rights
  | _ -> false
