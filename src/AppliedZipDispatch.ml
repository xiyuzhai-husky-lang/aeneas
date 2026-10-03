(** Source SliceZip classifier remains unchanged; new pinned mixed instances
    are considered only after it declines, and only after entrypoint admission. *)
type orientation = SliceSlice | SliceVec | VecSlice
let enabled () = AppliedBuiltins.enabled () || AppliedMixedZip.enabled ()
let classify_trait crate tr =
  match AppliedBuiltins.classify_trait crate tr with
  | Some (a,b) -> Some (SliceSlice,a,b)
  | None -> Option.map (fun (k,a,b) -> ((match k with AppliedMixedZip.SliceVec -> SliceVec | VecSlice -> VecSlice),a,b))
      (AppliedMixedZip.classify_trait crate tr)
let classify_function crate id args =
  match AppliedBuiltins.classify_function crate id args with
  | Some (meth,args) -> Some ((SliceSlice,meth),args)
  | None -> Option.map (fun ((k,meth),args) -> (((match k with AppliedMixedZip.SliceVec -> SliceVec | VecSlice -> VecSlice),meth),args))
      (AppliedMixedZip.classify_function crate id args)
let classify_function_checked span crate id generics =
  let selected = classify_function crate id generics in
  if enabled () && AppliedBuiltins.is_zip_iterator_method crate id && Option.is_none selected then
    [%craise_opt_span] span "Unsupported applied Zip method: no admitted exact iterator witnesses and supported ABI";
  selected
