(** Private pinned-input admission for the mixed Zip experiment.
    This is an executable scope restriction, not a proof of native Drop or
    unsafe standard-library correspondence. No caller-created record is trusted. *)
type token = Admitted
let current : token option ref = ref None
let token () = !current
let allowlist = [
  "7040c8d8a8866ad29efad5104c871afdda5700618c0831afa434fa45228a6737"; (* reviewed actual reify/evaluate input *)
  "cf2cebfedccfeffb3ff2cab56b356fda9419e3f424131abc5aea32a8f1a51d0d"; (* slice_vec_next.json *)
  "fba9bf48ea87d1307d959deddb60c29459dd32835ae4ec089922f6b57c01e624"; (* slice_vec_fold.json *)
  "a73275c1e43e7f7bd5c998a22df1523c33e918e9380c11fb6e842296d8fb3f9d"; (* slice_vec_dictionary.json *)
  "7e0ee5840029a7c689e7911128b66442d0562e6351e049fb9ae860b18e4fe092"; (* slice_vec_parent.json *)
  "a9b3c536641657e4ba521da4bcb6aaa14c5954e57c8f72c48e6220f82115573e"; (* slice_vec_resumed.json *)
  "6b9a4e350059e4f04ab1b8511a0c6f8861f75a8ecc5b7eb66b784450450e61a6"; (* vec_slice_next.json *)
  "0115f0e07dc27cfaa14242e327a9bd7016103d77114c1384b2a8039432699205"; (* vec_slice_fold.json *)
  "bf2bf21c90725b664f8d560bfa5fdd3beeead75a07df069af3d61b1cd0516917"; (* vec_slice_dictionary.json *)
  "385b8395f27d9e3748653240f3825b48a0d68eb5bf8452545986e848a20060b4"; (* vec_slice_parent.json *)
  "ab39c49f3861561da71db6998a35c7029611d654e41e17b67924e1155f61aa1f"; (* vec_slice_resumed.json *)
  "35ab8f9c57a6e78976ceee22ff33b254e9615824e4f337e99bdbc10857a2f6b2"; (* generic_zip.json *)
  "666c6982b03b891e0656845e215cbeb1330ec20775c2d9c659390347445473cf"; (* generic_and_concrete.json *)
  "2331e7bd297dd79c1c9ff42a412a8f614cf37a553e801c684d80c825af4f94f0"; (* mutable_names.json *)
]

let read_all ic =
  let b = Buffer.create 4096 in
  (try while true do Buffer.add_channel b ic 4096 done with End_of_file -> ());
  Buffer.contents b

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> read_all ic)

(** No shell, no input filename or reopening: hash exactly the supplied bytes.
    The pinned system SHA256 implementation is part of this private tool boundary. *)
let sha256 bytes =
  let argv = [|"/usr/bin/shasum"; "-a"; "256"|] in
  let output, input, error = Unix.open_process_args_full argv.(0) argv [| "LC_ALL=C"; "PATH=/usr/bin:/bin" |] in
  output_string input bytes;
  close_out input;
  let result = read_all output and errors = read_all error in
  let status = Unix.close_process_full (output, input, error) in
  let hex c = (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') in
  if status <> Unix.WEXITED 0 || errors <> "" || String.length result <> 68
     || String.sub result 64 4 <> "  -\n"
     || not (String.for_all hex (String.sub result 0 64)) then
    failwith "mixed Zip admission: SHA256 subprocess failed or malformed output";
  String.sub result 0 64

let field k = function `Assoc fields -> List.assoc k fields | _ -> failwith "expected object"
let string = function `String x -> x | _ -> failwith "expected string"
let bindings = function `Assoc xs -> xs | _ -> failwith "expected object"
let check condition message = if not condition then failwith ("mixed Zip admission: " ^ message)

(** The complete supplied crate must contain only ordinary files/directories.
    No ignored subtrees, symlinks, build scripts or extra Cargo configuration. *)
let source_files root =
  let rec walk rel =
    let path = if rel = "" then root else Filename.concat root rel in
    match (Unix.lstat path).Unix.st_kind with
    | Unix.S_REG -> [rel]
    | Unix.S_DIR ->
        Sys.readdir path |> Array.to_list |> List.sort String.compare
        |> List.concat_map (fun name -> walk (if rel = "" then name else Filename.concat rel name))
    | _ -> failwith "mixed Zip admission: non-regular source entry" in
  List.sort String.compare (walk "")

let load ~record_path ~source_root ~filename =
  current := None;
  try
    check (record_path <> "" && source_root <> "") "record and source root are required";
    check (Config.backend () = Config.Lean && !Config.filter_trait_impl_methods)
      "requires Lean and the explicit supported trait-method subset";
    let record_bytes = read_file record_path in
    check (List.mem (sha256 record_bytes) allowlist) "record is not approved by this candidate";
    let record = Yojson.Basic.from_string record_bytes in
    check (string (field "schema" record) = "mixed-zip-pinned-input-v1") "record schema";
    let files = bindings (field "files" record) in
    check (source_files source_root = List.sort String.compare (List.map fst files)) "source inventory differs";
    List.iter (fun (name, expected) ->
      check (sha256 (read_file (Filename.concat source_root name)) = string expected)
        ("source bytes differ: " ^ name)) files;
    let frontend = field "frontend" record in
    List.iter (fun (path, expected) -> check (sha256 (read_file path) = string expected)
      ("frontend binary differs: " ^ path)) (bindings (field "executables" frontend));
    (* The approved record digest binds the complete command and environment,
       not a caller-provided description. The LLBC digest binds its exact result. *)
    let bytes = read_file filename in
    check (sha256 bytes = string (field "llbc_sha256" record)) "LLBC bytes differ";
    match LlbcOfJson.crate_of_json (Yojson.Basic.from_string bytes) with
    | Error e -> Error e
    | Ok crate -> current := Some Admitted; Ok crate
  with exn -> Error (Printexc.to_string exn)
