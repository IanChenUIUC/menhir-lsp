open Menhir_lsp_lib
module M = MenhirSyntax
module MR = MenhirSyntax.Range
module Json = Yojson.Safe
include Menhir_lsp_lib.Utils
module Ivl_map = Interval_map.Make (Int)
module Ivl = Ivl_map.Interval

type document = Text_document.t

let no_implementation_hint uri =
  let filename = Uri.to_path uri in
  let base = Filename.basename filename in
  let kind =
    match Filename.extension filename with ".mll" -> `Mll | ".mly" | _ -> `Mly
  in
  let slug = base |> Filename.remove_extension in
  spr
    "Hint: did you declare the module '%s' in the '%s' stanza of the library's \
     dune file? If not, add the following line and try calling 'dune build':\n\
     %s\n"
    slug
    (match kind with `Mll -> "ocamllex" | `Mly -> "menhir")
    (md_fenced
    @@
    match kind with
    | `Mll -> spr "(ocamllex %s)" slug
    | `Mly -> spr "(menhir (modules %s))" slug)

let server_name = "menhir-lsp"

let compile_completions ?(range : Range.t option) ~(kind : CompletionItemKind.t)
    :
    (string * string option * string option * string list) list ->
    CompletionItem.t list =
  L.map (fun (label, detail, snippet, docs) ->
      CompletionItem.create ~kind ~label ~filterText:label
        ?labelDetails:
          (O.map
             (fun detail -> CompletionItemLabelDetails.create ~detail ())
             detail)
        ?textEdit:
          O.(
            let+ r = range in
            `TextEdit TextEdit.{ newText = label; range = r })
          (* note: snippets aren't allowed in text edit mode :( *)
        ?insertText:snippet
        ?insertTextFormat:(O.map (fun _ -> InsertTextFormat.Snippet) snippet)
        ?documentation:
          (match docs with
          | [] -> None
          | _ ->
              Some
                (`MarkupContent
                   (MarkupContent.create ~kind:Markdown
                      ~value:(String.concat "\n\n" docs))))
        ())

let _build_dir = ref None

(** The nearest ancestor of the working directory that contains [_build]. *)
let find_build_root () =
  let rec up dir =
    if Sys.file_exists (Filename.concat dir "_build") then Some dir
    else
      let parent = Filename.dirname dir in
      if String.equal parent dir then None else up parent
  in
  up (Sys.getcwd ())

let get_build_dir () =
  (* [dune describe] fails while dune runs in watch mode, which locks the build
     directory; fall back to the default build context. *)
  let fallback msg =
    match find_build_root () with
    | Some root ->
        let dir = (root, "_build/default") in
        _build_dir := Some dir;
        Ok dir
    | None -> Error msg
  in
  let f () =
    let default_msg = "Failure: dune describe." in
    try
      let inp = Unix.open_process_in "dune describe workspace" in
      let s = CCSexp.parse_chan inp in
      In_channel.close inp;
      match s with
      | Ok
          (`List
             (`List [ `Atom "root"; `Atom root_dir ]
             :: `List [ `Atom "build_context"; `Atom context ]
             :: _)) ->
          _build_dir := Some (root_dir, context);
          Ok (root_dir, context)
      | _ -> fallback default_msg
    with _ ->
      fallback
        (default_msg
       ^ "\n\
          Is dune running in watch mode?\n\
          menhir-lsp cannot analyze your project because dune --watch locks \
          the build directory.")
  in
  match !_build_dir with Some dir -> Ok dir | None -> f ()

(** e.g. if [uri] is

    [/home/foo/menhir-lsp/test/calc.mly]

    then [fetch_build_dir ~ext:".conflicts" uri] is

    [/home/foo/menhir-lsp/_build/default/test/calc.conflicts] *)
let fetch_build_dir ?(ext : string option) uri =
  let module P = Stdune.Path in
  let module F = Filename in
  let s_path = DocumentUri.to_path uri in
  let s_name = F.basename s_path in
  let s_slug = F.remove_extension s_name in
  let s_ext = O.get_or ~default:(F.extension s_name) ext in
  let msg = spr "No config found for %s." s_name in
  let open R in
  let* root, ctx = get_build_dir () in
  let p_root = P.of_string root in
  let p_dir = P.of_string (F.dirname s_path) in
  match P.drop_prefix p_dir ~prefix:p_root with
  | None -> Error msg
  | Some p_rel ->
      let p_ctx = P.of_string (F.concat root ctx) in
      let p_res = P.append_local p_ctx p_rel in
      let res = F.concat (P.to_string p_res) (s_slug ^ s_ext) in
      if Sys.file_exists res then Ok res else Error msg

module MK = Merlin_kernel
module QP = Query_protocol

let merlin_configs : (uri, MK.Mconfig.t) Hashtbl.t = Hashtbl.create 42

let get_merlin_config (uri : uri) =
  let path = DocumentUri.to_path uri in
  let dir = Filename.dirname path in
  let open O in
  let+ ctx, config_path = MK.Mconfig_dot.find_project_context dir in
  let dot, failures = MK.Mconfig_dot.get_config ctx path in
  log_info {|Search result for Merlin config of %s:
  Errors: %a|} path
    (pp_list pp_string) failures;
  let merlin =
    MK.Mconfig.merge_merlin_config dot MK.Mconfig.initial.merlin ~failures
      ~config_path
  in
  MK.Mconfig.normalize { MK.Mconfig.initial with merlin }

let find_merlin_config ~notify_back ~uri =
  let open O in
  match Hashtbl.find_opt merlin_configs uri with
  | None ->
      log_info ~notify_back
        "couldn't find merlin config for %s, generating new one"
        (DocumentUri.to_path uri);
      let+ config = get_merlin_config uri in
      Hashtbl.add merlin_configs uri config;
      config
  | o -> o

(** https://github.com/ocaml/ocaml-lsp/blob/master/ocaml-lsp-server/src/compl.ml
*)
let completion_kind kind : CompletionItemKind.t option =
  match kind with
  | `Value -> Some Value
  | `Variant -> Some EnumMember
  | `Label -> Some Field
  | `Module -> Some Module
  | `Modtype -> Some Interface
  | `MethodCall -> Some Method
  | `Keyword -> Some Keyword
  | `Constructor -> Some Constructor
  | `Type -> Some TypeParameter

(* Consider switching return type from options to more descriptive results *)
let with_merlin ~(doc : Text_document.t)
    (f : MK.Msource.t -> MK.Mpipeline.t -> 'a) =
  let open O in
  let+ config = get_merlin_config (TD.documentUri doc) in
  let source = MK.Msource.make (TD.text doc) in
  let pipeline = MK.Mpipeline.make config source in
  MK.Mpipeline.with_pipeline pipeline (fun () -> f source pipeline)

let get_merlin_completions ~(uri : uri) ~(pos : Position.t) ?(query_pos = pos)
    (prefix : word) source pipeline =
  let open O in
  let logical_pos = Position.logical query_pos in
  let query =
    Query_protocol.Complete_prefix (prefix.v, logical_pos, [], false, true)
  in
  let compls = Query_commands.dispatch pipeline query in
  let sortText_of_index idx = Printf.sprintf "%04d" idx in
  (* Merlin wants the completion prefix to include the fully qualified module path,
      but the TextEdit range must not extend before the cursor position, otherwise the completion won't show.
      Reference: https://github.com/ocaml/ocaml-lsp/blob/master/ocaml-lsp-server/src/compl.ml *)
  let range =
    (let+ prefix = String.split_on_char '.' prefix.v |> L.last_opt in
     let len = String.length prefix in
     let character = pos.character - len in
     let start = { pos with character } in
     { Range.start; end_ = pos })
    |> get_or ~default:prefix.p
  in
  let compls =
    L.mapi
      (fun idx QP.Compl.{ name; kind; desc; _ } ->
        CompletionItem.create ~label:name ?kind:(completion_kind kind)
          ~sortText:(sortText_of_index idx) ~detail:desc
          ~textEdit:(`TextEdit { newText = name; range })
          ())
      compls.entries
  in
  log_info "# merlin completions: %d" (L.length compls);
  compls

let get_merlin_docs ~expression ~(doc : Text_document.t) ~(pos : Position.t) =
  let logical_pos = Position.logical pos in
  with_merlin ~doc (fun _source pipeline ->
      let query = Query_protocol.Document (expression, logical_pos) in
      let typ = Query_commands.dispatch pipeline query in
      match typ with
      | `Found s | `Builtin s -> s
      | `No_documentation | `Invalid_context | `Not_found _ | `Not_in_env _
      | `File_not_found _ ->
          "")

let odoc_to_md text =
  match Doc_to_md.translate text with
  | Doc_to_md.Raw d | Doc_to_md.Markdown d -> d

let make_md_hover ?range sections =
  let concat_sections = String.concat "\n***\n" in
  Hover.create
    ~contents:
      (`MarkupContent
         (MarkupContent.create ~kind:Markdown ~value:(concat_sections sections)))
    ?range ()

let get_merlin_type ~(doc : Text_document.t) ~(pos : Position.t) expression =
  let open O in
  let logical_pos = Position.logical pos in
  let expr =
    with_merlin ~doc (fun _source pipeline ->
        let query = Query_protocol.Type_expr (expression, logical_pos) in
        let typ = Query_commands.dispatch pipeline query in
        typ)
  in
  let _search () =
    with_merlin ~doc (fun _source pipeline ->
        let query =
          Query_protocol.Type_search (expression, logical_pos, 0, true)
        in
        let typs = Query_commands.dispatch pipeline query in
        spr "%a"
          (Format.pp_print_list (fun out typ ->
               pf out "%s, %s" typ.Query_protocol.typ typ.Query_protocol.name))
          typs)
  in
  let enclosing =
    with_merlin ~doc (fun _source pipeline ->
        let query = Query_protocol.Type_enclosing (None, logical_pos, Some 0) in
        let typs = Query_commands.dispatch pipeline query in
        spr "%a"
          (Format.pp_print_list (fun out typ ->
               pf out "%s"
               @@ match typ with _, `Index _, _ -> "" | _, `String s, _ -> s))
          typs)
  in
  let _locate () =
    with_merlin ~doc (fun _source pipeline ->
        let query = Query_protocol.Locate_type logical_pos in
        let typ = Query_commands.dispatch pipeline query in
        match typ with
        | `Builtin t | `Found (Some t, _) -> t
        | `Invalid_context | `Not_found _ | `At_origin | `Not_in_env _
        | `File_not_found _
        | `Found (None, _) ->
            "")
  in
  log "Type_expr: %a" pp_stropt expr;
  log "Type_enclosing: %a" pp_stropt enclosing;
  expr <+> enclosing

let get_merlin_compls ~uri ~pos word =
  with_merlin ~doc:word.td (get_merlin_completions ~uri ~pos word)

let get_merlin_definition ~(doc : Text_document.t) ~(pos : Position.t) =
  let logical_pos = Position.logical pos in
  with_merlin ~doc (fun _source pipeline ->
      let query = Query_protocol.Locate (None, `ML, logical_pos) in
      match Query_commands.dispatch pipeline query with
      | `Found (file, def_pos) -> Some (file, def_pos)
      | `Builtin s -> log "Locate: builtin %s" s; None
      | `Not_in_env s -> log "Locate: not in env %s" s; None
      | `File_not_found s -> log "Locate: file not found %s" s; None
      | `Not_found (s, _) -> log "Locate: not found %s" s; None
      | `Invalid_context -> log "Locate: invalid context"; None
      | `At_origin -> log "Locate: at origin"; None)
  |> O.flatten

let parse_ocaml_impl s =
  let lexbuf = Lexing.from_string s in
  let msg = "OCaml syntax error" in
  try Ok (Ppxlib.Parse.implementation lexbuf) with
  | Syntaxerr.Error err -> Error (msg, Syntaxerr.location_of_error err)
  | Lexer.Error (_, rng) -> Error (msg, rng)

let parse_ocaml_type s =
  let lexbuf = Lexing.from_string s in
  Ppxlib.Parse.core_type lexbuf

let add_range ~parent_ref range =
  let add () =
    parent_ref := O.some @@ SelectionRange.create ?parent:!parent_ref ~range ()
  in
  (* Add [range] only if it preserves the invariant. *)
  match !parent_ref with
  | None -> add ()
  | Some p when Range.contains p.range range -> add ()
  | Some _ -> epr "Skipping bad selection range: %a." Range.pp range

let query_position (intervals : 'zone Ivl_map.t) offset : 'zone option =
  let open O in
  let query = Ivl.create (Included offset) (Included offset) in
  let res = Ivl_map.query_interval ~order:Desc query intervals in
  let* (ivl, zones), gen = Ivl_map.Gen.next res in
  let+ innermost_zone = L.head_opt zones in
  innermost_zone

let pp_interval out ({ low; high } : Ivl.t) =
  let open Ivl_map.Bound in
  let pp_low out = function
    | Included v -> pf out "[%d" v
    | Excluded v -> pf out "(%d" v
    | Unbounded -> pf out "(∞"
  in
  let pp_high out = function
    | Included v -> pf out "%d]" v
    | Excluded v -> pf out "%d)" v
    | Unbounded -> pf out "∞)"
  in
  pf out "%a, %a" pp_low low pp_high high

let show_interval = spr "%a" pp_interval

let pp_uri_debug out (uri : uri) =
  pf out "%s{hash = %d; query = %a}" (Uri.to_path uri) (Uri.hash uri)
    (pp_option pp_string) (Uri.query uri)

let pp_uri out (uri : uri) = pf out "%s" (Uri.to_path uri)
let pp_short_uri = pp_uri
let pp_short_state = fun out _ -> pf out "<state>"

let rec pp_selection_range (out : Format.formatter) (sr : SelectionRange.t) =
  pf out "%a%a" Range.pp sr.range
    (Format.pp_print_option (fun out p -> pf out " --> %a" pp_selection_range p))
    sr.parent

let get_ocaml_impl uri =
  fetch_build_dir ~ext:".ml" uri
  |> R.map_err (fun msg ->
      Diagnostic.create ~severity:Hint
        ~message:
          (`String
             (msg
             ^
             (* todo: use variants *)
             if String.starts_with ~prefix:"No config" msg then
               "\n\n" ^ no_implementation_hint uri
             else ""))
        ~source:server_name ~range:Range.first_line ())

let get_ocaml_intf = fetch_build_dir ~ext:".mli"

let read_file_contents filename =
  let ic = open_in filename in
  let contents = really_input_string ic (in_channel_length ic) in
  close_in ic;
  contents

(** Replaces the line directives of [text] with blanks of the same length.
    Merlin renumbers the lines that follow a directive, while queries on the
    implementation use its physical positions. *)
let blank_line_directives text =
  let is_directive line =
    String.length line > 1
    && line.[0] = '#'
    &&
    let rest = String.trim (String.sub line 1 (String.length line - 1)) in
    rest <> "" && match rest.[0] with '0' .. '9' -> true | _ -> false
  in
  String.split_on_char '\n' text
  |> L.map (fun line ->
      if is_directive line then String.make (String.length line) ' ' else line)
  |> String.concat "\n"

let get_source_map uri =
  let log s = log_src "get_source_map" s in
  match get_ocaml_impl uri with
  | Ok path ->
      let text = read_file_contents path in
      let doc = TD.create ~text:(blank_line_directives text) (Uri.of_path path) in
      let sourcemap =
        text |> Lexing.from_string
        |> Menhir_lsp_lib.Line_directives.read_line_directives []
      in
      (Some doc, sourcemap)
  | Error _ ->
      log "No source map for %a" pp_short_uri uri;
      (None, [])

(** Maps a location in a lexer / parser's source code to a symbol in the
    corresponding implementation generated by either Menhir or ocamllex.

    A symbol [v] at line [l] and column [c] in the source code is mapped to a
    symbol [v' = v] at line [m < m'] and column [d] of the implementation code
    that is characterized by a section with the following format:

    {v
    # l "path/to/source.(mly|mll)"
                                 v'
    \_______ c columns _________/
    # m' "path/to/source.ml"
    v} *)
let lookup_source (sourcemap : Line_directives.source_mapping list)
    ((startp, endp) as src_pos : lexing_range) (src_text : string) :
    lexing_range option =
  let open Line_directives in
  let open L in
  let log s = log_src "lookup_source" s in
  let start_col = startp.pos_cnum - endp.pos_bol in
  let end_col = endp.pos_cnum - endp.pos_bol in
  let@*? i, m = sourcemap in
  (* log "Comparing %a with mapping #%d %a " Range.pp_lexing src_pos i
    pp_source_mapping m; *)
  (* The text in the implementation has the same number of lines as the original action source text, plus a blank line we omit. *)
  let lines = String.split_on_char '\n' m.text in
  let lines = L.(take (length lines - 1) lines) in
  (* Scan the lines of this implementation section for the symbol we're looking for *)
  let@*? j, line = lines in
  let open O in
  let* _ = guard (m.src_line + j = startp.pos_lnum) in
  try
    let sub = String.sub line start_col (String.length src_text) in
    let* _ = guard (String.equal sub src_text) in
    (* log "At line #%d |%s| ('%s' = '%s')"
      (m.impl_line - L.length lines + j - 1)
      (String.escaped line) sub src_text; *)
    let m_startp, _m_endp = m.range in
    (* Reconstruct the range of the query symbol in the implementation. *)
    let bol =
      L.(take j lines |> fold_left (fun acc l -> acc + String.length l + 1) 0)
      + m_startp.pos_cnum
    in
    let line_startp =
      { m_startp with pos_lnum = m_startp.pos_lnum + j; pos_bol = bol }
    in
    let res_startp = { line_startp with pos_cnum = bol + start_col } in
    let res_endp = { line_startp with pos_cnum = bol + end_col } in
    let res = (res_startp, res_endp) in
    log "Success: %a --> %a" Range.pp_lexing src_pos Range.pp_lexing res;
    Some res
  with Invalid_argument _ -> None

(** Maps a line of the source code to the start of the code in the
    implementation section generated from it. Unlike [lookup_source], this does
    not depend on the contents of the line, which may be newer than the
    implementation. *)
let lookup_section (sourcemap : Line_directives.source_mapping list)
    (src_lnum : int) : Lexing.position option =
  let open Line_directives in
  let open O in
  let* m =
    L.find_opt
      (fun m ->
        let n = L.length (String.split_on_char '\n' m.text) - 1 in
        m.src_line <= src_lnum && src_lnum < m.src_line + n)
      sourcemap
  in
  let m_startp, _ = m.range in
  let+ i =
    Seq.init (String.length m.text) Fun.id
    |> Seq.find (fun i -> not (String.contains " \t\r\n" m.text.[i]))
  in
  let before = String.sub m.text 0 i in
  let newlines = L.length (String.split_on_char '\n' before) - 1 in
  let pos_bol =
    String.rindex_opt before '\n'
    >|= (fun k -> m_startp.pos_cnum + k + 1)
    |> get_or ~default:m_startp.pos_bol
  in
  {
    m_startp with
    pos_lnum = m_startp.pos_lnum + newlines;
    pos_bol;
    pos_cnum = m_startp.pos_cnum + i;
  }

(** Finds [name] in the code Menhir generates itself, outside every section
    copied from the source. This is where the OCaml types of [%type]
    declarations appear, which have no line directives. *)
let lookup_generated (sourcemap : Line_directives.source_mapping list)
    (impl : Text_document.t) (name : string) : Position.t option =
  let open Line_directives in
  let text = TD.text impl in
  let len = String.length name in
  let is_ident_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' | '.' -> true
    | _ -> false
  in
  let is_whole i =
    (i = 0 || not (is_ident_char text.[i - 1]))
    && (i + len = String.length text || not (is_ident_char text.[i + len]))
  in
  let in_section i =
    L.exists
      (fun m ->
        let startp, endp = m.range in
        startp.pos_cnum <= i && i < endp.pos_cnum)
      sourcemap
  in
  let rec find start =
    match CCString.find ~start ~sub:name text with
    | -1 -> None
    | i when in_section i || not (is_whole i) -> find (i + 1)
    | i ->
        let last = i + len - 1 in
        let before = String.sub text 0 last in
        let line = L.length (String.split_on_char '\n' before) - 1 in
        let bol = String.rindex_opt before '\n' |> O.map_or ~default:0 succ in
        Some ({ line; character = last - bol } : Position.t)
  in
  find 0
