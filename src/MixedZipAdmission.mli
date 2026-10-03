(** Constructor and mutable admission state are private to the loader. *)
type token
val token : unit -> token option
val load : record_path:string -> source_root:string -> filename:string -> (LlbcAst.crate, string) result
