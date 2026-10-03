(** Applied FnOnce ABI for a native closure with exactly one mutable capture.
    This selects a pure result type; no LLBC signature, borrow or continuation
    is edited. The ordinary FnOnce dictionary carries the native returned
    closure as part of its output, so callers cannot discard the write-back. *)
open Types
open LlbcAst

let ( let* ) = Option.bind

let enabled () = Config.backend () = Config.Lean
  && Sys.getenv_opt "AENEAS_EXPERIMENTAL_SHARED_PACKET_SIGNATURE" = Some "1"

let borrow_free infos ty =
  let info = TypesAnalysis.analyze_ty None infos ty in
  not (info.contains_borrow || info.contains_mut_borrow || info.contains_static)

let closure_has_single_mutable_capture (crate : crate) infos self =
  match self with
  | TAdt {id;generics;builtin=None} ->
      (match TypeDeclId.Map.find_opt id crate.type_decls with
      | Some decl when not decl.item_meta.has_errors
          && AppliedBuiltins.args_fit decl.generics generics ->
          (match decl.src,decl.kind with
          | ClosureType info,Struct _ when info.kind=FnOnce
              && info.fn_mut_impl=None && info.fn_impl=None ->
              let fields = Substitute.type_decl_get_instantiated_field_types decl None generics in
              let refs = List.filter_map (function
                | TRef (((RVar(Free _) | RBody _) as region),referent,kind)
                    when borrow_free infos referent ->
                    (* Function operands retain body-local regions. Native
                       signature instantiation maps each such name consistently
                       to a fresh free region; keep that original identity here. *)
                    Some(region,kind)
                | _ -> None) fields in
              List.length refs=List.length fields
              && List.length(List.filter (fun (_,kind) -> kind=RMut) refs)=1
              && List.length(List.sort_uniq compare (List.map fst refs))=List.length refs
          | _ -> false)
      | _ -> false)
  | _ -> false

let classify_trait (crate : crate) infos (tr : trait_decl_ref) =
  if not (enabled ()) then None else
  let* decl=TraitDeclId.Map.find_opt tr.id crate.trait_decls in
  if not (AppliedBuiltins.path decl.item_meta ["core";"ops";"function";"FnOnce"])
    then None else
  match tr.generics with
  | {regions=[];types=[self;argument;output];const_generics=[];trait_refs=[]}
    when closure_has_single_mutable_capture crate infos self
      && borrow_free infos argument && borrow_free infos output -> Some self
  | _ -> None

let classify_witness (crate : crate) infos (tr : trait_ref) =
  if tr.trait_decl_ref.binder_regions<>[] then None else
  let* self=classify_trait crate infos tr.trait_decl_ref.binder_value in
  match tr.kind with
  | TraitImpl impl ->
      let* (_,_,actual)=AppliedBuiltins.instantiate_impl crate impl in
      if equal_trait_decl_ref actual tr.trait_decl_ref.binder_value then Some self else None
  | _ -> None
