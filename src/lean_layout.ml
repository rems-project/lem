(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*  Lean backend: layout of the generated text.                          *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2025 by the Lem authors; see the   *)
(*  licence header of lean_backend.ml.                                    *)
(**************************************************************************)

(* Re-lays out a generated Lean file so that it reads like the source:
   long declarations are broken over several lines, match arms sit one per
   line, nested matches, lambdas and `let`s are indented, and the author's
   comments stay next to their code.

   The pass is text-only and token-preserving: it changes nothing but the
   whitespace BETWEEN tokens. Where the input has no whitespace between two
   tokens (`).f`, `x@(`, `(f`), none is added; where it has whitespace, the
   pass emits a space or a line break with indentation (a space after a `,`
   or `;` is also allowed, since those are delimiter tokens). The
   declaration census of both consumers is the exit test.

   Lean's layout is column-sensitive. The shapes emitted here were checked
   on Lean 4.32.2; the rules relied on are:
   - the alternatives of one `match` must all start at a column ≥ the first
     alternative's column, and an alternative's right-hand side must start
     at a column ≥ its `|` — so every alternative starts its own line at the
     `match`'s indentation, and a right-hand side that does not fit on that
     line moves to the next line, indented by two;
   - the arguments of an application on a continuation line must be right
     of the innermost enclosing position anchor (the `let` keyword, the
     first `|`, the first field of a structure instance, column 0 at top
     level; parentheses reset it) — so a `let`, a `match` and the fields of
     a structure instance are indented relative to the column of their own
     keyword or first field (Align), every other continuation line is
     indented more than the line that opened its construct, and a comment
     in front of a `let` or `match` goes on a line of its own.

   Fail closed: a declaration the parser below does not fully understand
   (an unknown keyword, an unbalanced bracket, a `let` without `;`, a `--`
   comment) is left exactly as it was, with any multi-line comment inside
   it folded onto one line as before this pass. *)

(* ---------------------------------------------------------------------- *)
(* 1. Documents and the Wadler/Leijen printer                              *)
(* ---------------------------------------------------------------------- *)

type doc =
  | Nil
  | Text of string            (* no line break inside *)
  | MLText of string          (* text with line breaks (a multi-line comment);
                                 never fits on a line *)
  | Line                      (* a space when flat, a line break when broken *)
  | HardLine                  (* always a line break *)
  | Nest of int * doc
  | Align of doc              (* indentation set to the current column *)
  | Cat of doc * doc
  | Group of doc              (* flat if it fits, else its Lines break *)
  | Flat of doc               (* forced flat (fails to fit if it has a hard break) *)
  | Union of doc * doc        (* the first if its first line fits, else the second *)

let ( ^^ ) a b = match a, b with Nil, _ -> b | _, Nil -> a | _ -> Cat (a, b)
let cat ds = List.fold_left ( ^^ ) Nil ds
let text s = if s = "" then Nil else Text s
let nest n d = if d = Nil then Nil else Nest (n, d)
let group d = if d = Nil then Nil else Group d

(* display width: UTF-8 code points *)
let width s =
  let n = ref 0 in
  String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr n) s;
  !n

let last_line s =
  match String.rindex_opt s '\n' with
  | None -> s
  | Some i -> String.sub s (i + 1) (String.length s - i - 1)

type mode = Flat_m | Break_m
type sdoc = SText of string | SLine of int | SFail

let rec be w k (stack : (int * mode * doc) list) : sdoc Seq.t = fun () ->
  match stack with
  | [] -> Seq.Nil
  | (i, m, d) :: z ->
    (match d with
     | Nil -> be w k z ()
     | Cat (a, b) -> be w k ((i, m, a) :: (i, m, b) :: z) ()
     | Nest (j, a) -> be w k ((i + j, m, a) :: z) ()
     | Align a -> be w k ((k, m, a) :: z) ()
     | Text s -> Seq.Cons (SText s, be w (k + width s) z)
     | MLText s ->
       (* in flat mode this cannot fit; the text is still emitted, so no
          layout decision can ever lose a comment *)
       (match m with
        | Flat_m -> Seq.Cons (SFail, Seq.cons (SText s) (be w (width (last_line s)) z))
        | Break_m -> Seq.Cons (SText s, be w (width (last_line s)) z))
     | Line ->
       (match m with
        | Flat_m -> Seq.Cons (SText " ", be w (k + 1) z)
        | Break_m -> Seq.Cons (SLine i, be w i z))
     | HardLine ->
       (match m with
        | Flat_m -> Seq.Cons (SFail, be w k z)
        | Break_m -> Seq.Cons (SLine i, be w i z))
     | Flat a -> be w k ((i, Flat_m, a) :: z) ()
     | Group a ->
       (match m with
        | Flat_m -> be w k ((i, Flat_m, a) :: z) ()
        | Break_m ->
          (* The candidate is memoized (call-by-need), which Wadler's
             complexity argument assumes: [fits] scans it, and if it fits
             the same stream is emitted, so every group decision on the line
             is made once. Without the sharing a candidate's tail was
             recomputed by each consumer, and each recomputation re-decided
             every Break-mode group that followed on the line: exponential
             in the number of sibling groups on a line that overflows the
             width (a 47-wide constructor pattern took over two minutes,
             45 took none). *)
          let flat = Seq.memoize (be w k ((i, Flat_m, a) :: z)) in
          if fits (w - k) flat then flat ()
          else be w k ((i, Break_m, a) :: z) ())
     | Union (a, b) ->
       (match m with
        | Flat_m -> be w k ((i, Flat_m, a) :: z) ()
        | Break_m ->
          let first = Seq.memoize (be w k ((i, Break_m, a) :: z)) in
          if fits (w - k) first then first ()
          else be w k ((i, Break_m, b) :: z) ()))

(* does the output fit in [w] columns up to the next line break? *)
and fits w (s : sdoc Seq.t) =
  if w < 0 then false
  else match s () with
    | Seq.Nil -> true
    | Seq.Cons (SText t, rest) -> fits (w - width t) rest
    | Seq.Cons (SLine _, _) -> true
    | Seq.Cons (SFail, _) -> false

(* Render [d] at indentation [indent] into the lines the printer makes. A
   line is what lies between two of the printer's own breaks; the text of a
   token is copied as it is, line breaks inside it included (a multi-line
   comment or string literal), so only the printer's own separators are
   trimmed: a line's trailing spaces (a token never ends in a space) and a
   line holding nothing but indentation. *)
let render ~width:w ~indent d : string list =
  let lines = ref [] in
  let cur = Buffer.create 256 in
  let flush_line () =
    let s = Buffer.contents cur in
    let n = ref (String.length s) in
    while !n > 0 && s.[!n - 1] = ' ' do decr n done;
    if !n > 0 then lines := String.sub s 0 !n :: !lines;
    Buffer.clear cur
  in
  Buffer.add_string cur (String.make indent ' ');
  let rec go s = match s () with
    | Seq.Nil -> ()
    | Seq.Cons (SText t, rest) -> Buffer.add_string cur t; go rest
    | Seq.Cons (SLine i, rest) -> flush_line (); Buffer.add_string cur (String.make i ' '); go rest
    | Seq.Cons (SFail, rest) ->  (* cannot happen outside a lookahead *)
      flush_line (); Buffer.add_string cur (String.make indent ' '); go rest
  in
  go (be w indent [ (indent, Break_m, d) ]);
  flush_line ();
  List.rev !lines

(* ---------------------------------------------------------------------- *)
(* 2. Lexer (the conventions of lean_backend.ml's normalize_layout)         *)
(* ---------------------------------------------------------------------- *)

type kind = Word | Open | Close | Comma | Semi | Str | Comment | LineComment | Nl

type tok = {
  s : string;
  k : kind;
  ws : bool;      (* whitespace (or a line break) right before it *)
  nl : bool;      (* it is the first token of a physical line *)
  col : int;      (* column of its first byte *)
  pos : int;      (* byte offset *)
}

let is_ident_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
  || c = '_' || c = '\'' || c = '.' || Char.code c >= 128

(* s.[i] = '\'': the index of the closing quote if a character literal
   starts here — an escape or one UTF-8 character of one to four bytes — else
   None (the rule of lean_backend.ml's normalize_spacing) *)
let char_literal_end (s : string) i =
  let n = String.length s in
  if i + 1 >= n then None
  else if s.[i + 1] = '\\' then
    (try Some (String.index_from s (i + 3) '\'') with Not_found | Invalid_argument _ -> None)
  else begin
    let c = Char.code s.[i + 1] in
    let len = if c < 0x80 then 1 else if c land 0xE0 = 0xC0 then 2
      else if c land 0xF0 = 0xE0 then 3 else if c land 0xF8 = 0xF0 then 4 else 1 in
    if i + 1 + len < n && s.[i + 1 + len] = '\'' then Some (i + 1 + len) else None
  end

let lex (s : string) : tok array =
  let n = String.length s in
  let out = ref [] in
  let col = ref 0 and ws = ref false and nl = ref true in
  let push k i j =
    out := { s = String.sub s i (j - i); k; ws = !ws; nl = !nl; col = !col; pos = i } :: !out;
    (* columns after a token: only used for the first token of a line *)
    col := !col + (j - i); ws := false; nl := false
  in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    if c = ' ' || c = '\t' then (ws := true; incr col; incr i)
    else if c = '\n' then begin
      out := { s = "\n"; k = Nl; ws = false; nl = false; col = !col; pos = !i } :: !out;
      col := 0; ws := true; nl := true; incr i
    end
    else if c = '"' then begin
      let j = ref (!i + 1) in
      let stop = ref false in
      while not !stop && !j < n do
        if s.[!j] = '\\' && !j + 1 < n then j := !j + 2
        else if s.[!j] = '"' then (incr j; stop := true)
        else incr j
      done;
      push Str !i !j; i := !j
    end
    else if c = '/' && !i + 1 < n && s.[!i + 1] = '-' then begin
      let depth = ref 1 and j = ref (!i + 2) in
      while !depth > 0 && !j < n do
        if !j + 1 < n && s.[!j] = '/' && s.[!j + 1] = '-' then (incr depth; j := !j + 2)
        else if !j + 1 < n && s.[!j] = '-' && s.[!j + 1] = '/' then (decr depth; j := !j + 2)
        else incr j
      done;
      push Comment !i !j; i := !j
    end
    else if c = '-' && !i + 1 < n && s.[!i + 1] = '-' then begin
      let j = (try String.index_from s !i '\n' with Not_found -> n) in
      push LineComment !i j; i := j
    end
    else if c = '\'' && (!i = 0 || not (is_ident_char s.[!i - 1])) && char_literal_end s !i <> None then begin
      let j = match char_literal_end s !i with Some j -> j | None -> assert false in
      push Word !i (j + 1); i := j + 1
    end
    else if c = '\xC2' && !i + 1 < n && s.[!i + 1] = '\xAB' then begin
      (* `«…»` is one identifier, spaces inside included *)
      let rec close k = if k + 1 >= n then n else if s.[k] = '\xC2' && s.[k + 1] = '\xBB' then k + 2 else close (k + 1) in
      let j = close (!i + 2) in
      push Word !i j; i := j
    end
    else if c = '(' || c = '[' || c = '{' then (push Open !i (!i + 1); incr i)
    else if c = ')' || c = ']' || c = '}' then (push Close !i (!i + 1); incr i)
    else if c = ',' then (push Comma !i (!i + 1); incr i)
    else if c = ';' then (push Semi !i (!i + 1); incr i)
    else begin
      (* a word: a run of identifier characters, or a run of symbol
         characters (so `x=>` and `:=y` are two tokens each, as for Lean) *)
      let cls d =
        if d = ' ' || d = '\t' || d = '\n' || d = '"' || d = '(' || d = ')' || d = '['
           || d = ']' || d = '{' || d = '}' || d = ',' || d = ';' then 0
        else if String.contains "-$%&*+/:<=>@^|~\\#" d then 2
        else 1
      in
      let c0 = cls c in
      let j = ref !i in
      let stop = ref false in
      while not !stop && !j < n do
        let d = s.[!j] in
        if cls d <> c0 then stop := true
        else if !j > !i && !j + 1 < n
                && ((d = '/' && s.[!j + 1] = '-') || (d = '-' && s.[!j + 1] = '-')) then stop := true
        else incr j
      done;
      push Word !i !j; i := !j
    end
  done;
  Array.of_list (List.rev !out)

(* ---------------------------------------------------------------------- *)
(* 3. Physical lines and layout units                                      *)
(* ---------------------------------------------------------------------- *)

type line = { indent : int; toks : tok list; start : int; stop_ : int }

let split_lines (s : string) (toks : tok array) : line list =
  let lines = ref [] in
  let cur = ref [] and start = ref 0 in
  let flush stop_ =
    let ts = List.rev !cur in
    let indent = match ts with t :: _ -> t.col | [] -> 0 in
    lines := { indent; toks = ts; start = !start; stop_ } :: !lines;
    cur := []
  in
  Array.iter (fun t ->
      if t.k = Nl then (flush t.pos; start := t.pos + 1) else cur := t :: !cur) toks;
  if !start < String.length s || !cur <> [] then flush (String.length s);
  List.rev !lines

let decl_kws = [ "def"; "theorem"; "abbrev"; "instance"; "example"; "opaque" ]
let modifier_kws = [ "partial"; "private"; "protected"; "noncomputable"; "unsafe"; "nonrec" ]
let other_cmds = [ "inductive"; "structure"; "class"; "mutual"; "end"; "namespace"; "section";
                   "open"; "export"; "import"; "attribute"; "set_option"; "deriving";
                   "termination_by"; "decreasing_by"; "where"; "universe"; "variable";
                   "axiom"; "macro"; "syntax"; "notation"; "infix"; "infixl"; "infixr"; "prefix" ]

let code_toks l = List.filter (fun t -> t.k <> Comment && t.k <> LineComment) l.toks
let is_blank l = l.toks = []
let comment_only l = l.toks <> [] && code_toks l = []

(* Some (index of the declaration keyword) for `[@[...]] [modifiers] kw` *)
let decl_head l =
  let ts = Array.of_list (code_toks l) in
  let n = Array.length ts in
  let i = ref 0 in
  if !i < n && ts.(!i).s = "@" && !i + 1 < n && ts.(!i + 1).k = Open && ts.(!i + 1).s = "[" then begin
    i := !i + 2;
    let depth = ref 1 in
    while !depth > 0 && !i < n do
      (if ts.(!i).k = Open then incr depth else if ts.(!i).k = Close then decr depth);
      incr i
    done
  end;
  while !i < n && List.mem ts.(!i).s modifier_kws do incr i done;
  if !i < n && List.mem ts.(!i).s decl_kws then Some !i else None

let ends_with_where l =
  match List.rev (code_toks l) with t :: _ -> t.s = "where" | [] -> false

(* a command line: `#eval`, `#check`, … (the `assert`s lem emits are
   `#eval do` blocks) *)
let is_hash_command l =
  match l.toks with t :: _ -> t.s <> "" && t.s.[0] = '#' | [] -> false

let is_boundary l =
  is_blank l || comment_only l || is_hash_command l
  || (match l.toks with
      | t :: _ -> t.s = "@" || List.mem t.s decl_kws || List.mem t.s modifier_kws
                  || List.mem t.s other_cmds
      | [] -> true)

type unit_ =
  | Verbatim of line
  | Decl of line list        (* a whole declaration: header line and its body lines *)
  | Single of line list      (* one item (a field, a constructor, a header) laid out on
                                its own, at its indentation; with the lines that close
                                its brackets *)

(* bracket depth after a line's tokens (negative if more close than open) *)
let depth_delta l =
  List.fold_left (fun d t -> match t.k with Open -> d + 1 | Close -> d - 1 | _ -> d) 0 l.toks

let split_units (lines : line list) : unit_ list =
  let rec go acc = function
    | [] -> List.rev acc
    | l :: rest when is_hash_command l ->
      (* a `#` command and the indented lines of its block are copied *)
      let rec take acc = function
        | l' :: rest' when l'.indent > l.indent && not (is_blank l') -> take (Verbatim l' :: acc) rest'
        | rest' -> (acc, rest')
      in
      let acc', rest' = take (Verbatim l :: acc) rest in
      go acc' rest'
    | l :: rest when decl_head l <> None && not (ends_with_where l) ->
      (* The declaration's body: every following line that is not the start
         of another item. A blank or comment-only line is inside the body if
         a bracket is still open, or if the next code line is a continuation
         (a `let` after a comment, a list element after a blank line);
         otherwise it is the record in front of the next item. *)
      let rec take depth body = function
        | l' :: rest' when not (is_boundary l') -> take (depth + depth_delta l') (l' :: body) rest'
        | l' :: rest' when (is_blank l' || comment_only l')
                        && (depth > 0
                            || (match List.find_opt (fun x -> not (is_blank x || comment_only x)) rest' with
                                | Some x -> not (is_boundary x)
                                | None -> false)) ->
          take depth (l' :: body) rest'
        | rest' -> (List.rev body, rest')
      in
      let body, rest' = take (depth_delta l) [] rest in
      go (Decl (l :: body) :: acc) rest'
    | l :: rest ->
      let single =
        if is_blank l || comment_only l then false
        else match l.toks with
          | t :: _ when t.s = "export" || decl_head l <> None -> true
          | t :: _ when List.mem t.s [ "inductive"; "structure"; "class" ] -> true
          | _ when is_boundary l -> false
          | _ -> true
      in
      if not single then go (Verbatim l :: acc) rest
      else begin
        (* the lines that close the item's brackets belong to it *)
        let rec take depth body = function
          | l' :: rest' when depth > 0 && not (is_blank l') && decl_head l' = None ->
            take (depth + depth_delta l') (l' :: body) rest'
          | rest' -> (List.rev body, rest')
        in
        let body, rest' = take (depth_delta l) [] rest in
        go (Single (l :: body) :: acc) rest'
      end
  in
  go [] lines

(* ---------------------------------------------------------------------- *)
(* 4. Parser: tokens of one unit → document                                *)
(* ---------------------------------------------------------------------- *)

exception Bail of string

type sep = NoSep | Space | Brk
type item = {
  d : doc;
  sep : sep;                    (* how it joins the previous item *)
  hug : (doc * doc) option;     (* `(fun … =>` head and body, for a trailing argument *)
  colon : bool;                 (* the token `:` *)
  anchor : bool;                (* a `let` or a `match`: it must start its line, so a
                                   comment in front of it goes on a line of its own *)
}
let item ?(sep = Brk) ?hug ?(colon = false) ?(anchor = false) d = { d; sep; hug; colon; anchor }
(* an item whose document was extended (a comment attached) no longer hugs:
   the hug layout prints the stored head and body, not [d] *)
let with_d it d = { it with d; hug = None }

let symbolic_chars = "-!$%&*+./:<=>?@^|~\\"
let unicode_ops = [ "\xE2\x86\x92" (* → *); "\xC3\x97" (* × *); "\xE2\x88\xA7" (* ∧ *);
                    "\xE2\x88\xA8" (* ∨ *); "\xE2\x89\xA0" (* ≠ *); "\xE2\x89\xA4" (* ≤ *);
                    "\xE2\x89\xA5" (* ≥ *); "\xC2\xAC" (* ¬ *); "\xE2\x88\x98" (* ∘ *);
                    "\xE2\x86\x94" (* ↔ *); "\xE2\x8A\x95" (* ⊕ *) ]
let is_operator s =
  s <> "" && (String.for_all (fun c -> String.contains symbolic_chars c) s || List.mem s unicode_ops)

let bad_kws = [ "do"; "by"; "have"; "show"; "calc"; "suffices"; "obtain"; "at"; "from"; "in";
                "deriving"; "termination_by"; "decreasing_by"; "mutual"; "end"; "where" ]

let is_terminator t =
  match t.k with
  | Close | Comma | Semi -> true
  | Word -> List.mem t.s [ "|"; "=>"; "then"; "else"; "with" ]
  | _ -> false

let has_nl s = String.contains s '\n'
let comment_doc t = if has_nl t.s then MLText t.s else Text t.s

let fold_comment s =
  Str.global_replace (Str.regexp "[ \t]*\n[ \t]*") " " s

type pending = Own of tok | Lead of tok

let parse_unit (toks : tok array) : doc =
  let n = Array.length toks in
  let p = ref 0 in
  let peek () = if !p < n then Some toks.(!p) else None in
  let advance () = incr p in
  (* a keyword or separator token, with a space before it iff the input had
     whitespace there (`x=>` stays `x=>`) *)
  let expect s = match peek () with
    | Some t when t.s = s -> advance (); (if t.ws then Text " " else Nil) ^^ Text s
    | Some t -> raise (Bail ("expected " ^ s ^ ", got " ^ t.s))
    | None -> raise (Bail ("expected " ^ s ^ " at end"))
  in
  (* an opening keyword (`fun`, `match`, `let`, `if`), with its following space *)
  let opener t = Text t.s ^^ (match peek () with Some x when x.ws -> Text " " | _ -> Nil) in
  (* the break before a body (`:= value`, `=> rhs`, …): a Line where the
     input had whitespace, nothing where it had none (`:=x` stays `:=x`) *)
  let body_sep () = match peek () with Some x when not x.ws -> Nil | _ -> Line in
  let sep_of t = if not t.ws then NoSep else if is_operator t.s || t.s = ":" || t.s = ":=" then Space else Brk in
  let sep_doc = function NoSep -> Nil | Space -> Text " " | Brk -> Line in
  (* inline comments right after a `,`, a `;` or `with`: they trail what came before *)
  let take_inline_comments () =
    let acc = ref Nil in
    let rec go () = match peek () with
      | Some t when t.k = Comment && not (t.nl || has_nl t.s) ->
        advance (); acc := !acc ^^ Text " " ^^ comment_doc t; go ()
      | _ -> ()
    in
    go (); !acc
  in
  let attach_leading cs it =
    let pre = cat (List.map (function
        | Own t -> comment_doc t ^^ HardLine
        | Lead t -> comment_doc t ^^ (if it.anchor then HardLine else Text " ")) cs) in
    let sep = match cs with (Own t | Lead t) :: _ -> if t.ws then Brk else it.sep | [] -> it.sep in
    if cs = [] then it else { (with_d it (pre ^^ it.d)) with sep }
  in
  let trailing_own cs =
    cat (List.map (function
        | Own t -> HardLine ^^ comment_doc t ^^ (if has_nl t.s then HardLine else Nil)
        | Lead t -> Text " " ^^ comment_doc t) cs)
  in
  (* items of a sequence (an application, a header, a pattern, …) *)
  let rec parse_items stop : item list =
    let items = ref [] in
    let pending = ref [] in
    let pending_at = ref 0 in
    let fin = ref false in
    while not !fin do
      match peek () with
      | None -> fin := true
      | Some t when stop t ->
        (* comments in front of the next alternative belong to it, not to
           the end of this sequence: leave them for the arm loop *)
        if !pending <> [] && t.s = "|" then (p := !pending_at; pending := []);
        fin := true
      | Some t when t.k = LineComment -> raise (Bail "line comment")
      | Some t when t.k = Comment ->
        if !pending = [] then pending_at := !p;
        advance ();
        if t.nl || has_nl t.s then pending := Own t :: !pending
        else begin
          match peek (), !items, !pending with
          | Some t', _, _ when not (stop t' || is_terminator t') && t'.k <> Comment ->
            pending := Lead t :: !pending
          | _, it :: rest, [] -> items := with_d it (it.d ^^ Text " " ^^ comment_doc t) :: rest
          | _ -> pending := Lead t :: !pending
        end
      | Some t when is_terminator t -> raise (Bail ("unexpected " ^ t.s))
      | Some t ->
        let it = parse_item stop t in
        let it = attach_leading (List.rev !pending) it in
        pending := [];
        items := it :: !items
    done;
    let items = match List.rev !pending with
      | [] -> !items
      | cs -> (match !items with
          | it :: rest -> with_d it (it.d ^^ trailing_own cs) :: rest
          | [] -> [ item (trailing_own cs) ])
    in
    List.rev items
  (* an application: the arguments fill the line, continuation lines at +n *)
  and fill ?(n = 2) items =
    match items with
    | [] -> Nil
    | first :: rest ->
      first.d ^^ nest n (cat (List.map (fun it ->
          match it.sep with Brk -> group (Line ^^ it.d) | s -> sep_doc s ^^ it.d) rest))
  (* A trailing `(fun … =>` argument hugs the line when everything before
     it, and its head, fit on that line; its body is then indented by two
     from the line, not from the argument column. This keeps a chain of
     monadic binds at two columns per level. *)
  and build_seq items =
    match List.rev items with
    | { hug = Some (head, body); sep = Brk; _ } :: (_ :: _ as rinit) ->
      let init = List.rev rinit in
      let first = List.hd init and mid = List.tl init in
      let hugged = Flat (first.d ^^ cat (List.map (fun it -> sep_doc it.sep ^^ it.d) mid)
                         ^^ Text " " ^^ head) ^^ body in
      group (Union (hugged, fill items))
    | _ -> fill items
  and parse_seq stop = build_seq (parse_items stop)
  and parse_item stop t : item =
    match t.k, t.s with
    | Open, ("(" | "[") -> advance (); parse_bracket t
    | Open, _ -> advance (); parse_brace t
    | Word, "fun" -> advance (); parse_fun stop t
    | Word, "match" -> advance (); parse_match stop t
    | Word, "let" -> advance (); parse_let stop t
    | Word, ("if" | "lem_if") -> advance (); parse_if stop t
    | Word, kw when List.mem kw bad_kws ->
      (* `where` may end a header (`instance : C T where /- c -/`) *)
      let only_comments_follow =
        let rec go i = i >= n || (toks.(i).k = Comment && go (i + 1)) in go (!p + 1) in
      if kw = "where" && only_comments_follow then (advance (); item ~sep:(sep_of t) (Text kw))
      else raise (Bail ("keyword " ^ kw))
    | (Word | Str), _ ->
      advance ();
      (* a token with line breaks inside (a string literal) is copied as it
         is and, like a multi-line comment, never fits on a line *)
      item ~sep:(sep_of t) ~colon:(t.s = ":") (if has_nl t.s then MLText t.s else Text t.s)
    | _ -> raise (Bail ("unexpected " ^ t.s))
  and parse_bracket t =
    let close = if t.s = "(" then ")" else "]" in
    let elems = ref [] in
    let rec loop () =
      let its = parse_items (fun x -> x.k = Close || x.k = Comma) in
      (match peek () with
       | Some x when x.k = Comma ->
         advance ();
         let trail = take_inline_comments () in
         elems := (build_seq its ^^ Text "," ^^ trail, None) :: !elems; loop ()
       | Some x when x.k = Close && x.s = close ->
         advance ();
         let hug = match its with [ { hug = Some h; _ } ] when t.s = "(" -> Some h | _ -> None in
         elems := (build_seq its, hug) :: !elems
       | Some x -> raise (Bail ("mismatched " ^ x.s))
       | None -> raise (Bail "unclosed bracket"))
    in
    loop ();
    match List.rev !elems with
    | [ (_, Some (head, body)) ] ->
      item ~sep:(sep_of t) ~hug:(Text t.s ^^ head, body ^^ Text close)
        (Text t.s ^^ group (head ^^ body) ^^ Text close)
    | elems ->
      let inner = match List.map fst elems with
        | [] -> Nil
        | [ d ] -> d
        | d :: rest -> d ^^ nest 2 (cat (List.map (fun e -> group (Line ^^ e)) rest))
      in
      item ~sep:(sep_of t) (Text t.s ^^ inner ^^ Text close)
  and parse_brace t =
    (* `{ f := v, … }` or `{ r with f := v, … }`: one field per line when broken *)
    let field_stop x = x.k = Close || x.k = Comma in
    let first = parse_seq (fun x -> field_stop x || x.s = "with") in
    let head, first_field = match peek () with
      | Some x when x.s = "with" ->
        advance ();
        let trail = take_inline_comments () in
        (Some (first ^^ Text " with" ^^ trail), parse_seq field_stop)
      | _ -> (None, first)
    in
    let fields = ref [ first_field ] in
    let rec loop () =
      match peek () with
      | Some x when x.k = Comma ->
        advance ();
        let trail = take_inline_comments () in
        (match !fields with f :: rest -> fields := (f ^^ Text "," ^^ trail) :: rest | [] -> ());
        fields := parse_seq field_stop :: !fields; loop ()
      | Some x when x.k = Close && x.s = "}" -> advance ()
      | Some x -> raise (Bail ("mismatched " ^ x.s))
      | None -> raise (Bail "unclosed brace")
    in
    loop ();
    let fields = List.rev !fields in
    let body = match fields with
      | [] -> Nil
      | f :: rest -> f ^^ cat (List.map (fun e -> Line ^^ e) rest)
    in
    let inner = match head with
      | Some h -> h ^^ Line ^^ body
      | None -> body
    in
    (* the fields align under the first one: Lean anchors the fields of a
       structure instance at the first field's column *)
    let d = if inner = Nil then Text "{ }" else group (Text "{ " ^^ Align inner ^^ Text " }") in
    item ~sep:(sep_of t) d
  and parse_fun stop t =
    let kw = opener t in
    let binders = parse_seq (fun x -> x.s = "=>") in
    let arrow = expect "=>" in
    let trail = take_inline_comments () in
    let sep = body_sep () in
    let body = parse_seq stop in
    let head = kw ^^ binders ^^ arrow ^^ trail in
    let body = nest 2 (sep ^^ body) in
    item ~hug:(head, body) (group (head ^^ body))
  and parse_arms stop =
    (* `| pat => rhs` alternatives, each on its own line, with the comments
       before an alternative on their own lines and the inline comments
       after a right-hand side trailing it *)
    let arms = ref [] in
    let own = ref [] in
    let fin = ref false in
    let head_trail = ref Nil in
    while not !fin do
      match peek () with
      | Some t when t.k = Comment && (t.nl || has_nl t.s) -> advance (); own := t :: !own
      | Some t when t.k = Comment ->
        advance ();
        (match !arms with
         | (cs, arm) :: rest when !own = [] -> arms := (cs, arm ^^ Text " " ^^ comment_doc t) :: rest
         | [] when !own = [] -> head_trail := !head_trail ^^ Text " " ^^ comment_doc t
         | _ -> own := t :: !own)
      | Some t when t.s = "|" ->
        advance ();
        let bar = opener t in
        let pats = ref [] in
        let rec loop () =
          pats := parse_seq (fun x -> x.s = "=>" || x.k = Comma) :: !pats;
          match peek () with
          | Some x when x.k = Comma -> advance (); loop ()
          | _ -> ()
        in
        loop ();
        let arrow = expect "=>" in
        let trail = take_inline_comments () in
        let sep = body_sep () in
        let rhs = parse_seq (fun x -> x.s = "|" || stop x) in
        let pat = match List.rev !pats with
          | [] -> Nil
          | p :: rest -> p ^^ nest 2 (cat (List.map (fun q -> Text "," ^^ group (Line ^^ q)) rest))
        in
        let arm = group (bar ^^ pat ^^ arrow ^^ trail ^^ nest 2 (sep ^^ rhs)) in
        arms := (List.rev !own, arm) :: !arms; own := []
      | _ -> fin := true
    done;
    if !arms = [] then raise (Bail "match without alternatives");
    let tail = cat (List.map (fun t ->
        HardLine ^^ comment_doc t ^^ (if has_nl t.s then HardLine else Nil)) (List.rev !own)) in
    let arms_doc = cat (List.map (fun (cs, arm) ->
        HardLine ^^ cat (List.map (fun c -> comment_doc c ^^ HardLine) cs) ^^ arm) (List.rev !arms)) in
    (!head_trail, arms_doc ^^ tail)
  and parse_match stop t =
    let kw = opener t in
    let discrs = ref [] in
    let rec loop () =
      discrs := parse_seq (fun x -> x.s = "with" || x.k = Comma) :: !discrs;
      match peek () with
      | Some x when x.k = Comma -> advance (); loop ()
      | _ -> ()
    in
    loop ();
    let with_ = expect "with" in
    let head_trail, arms = parse_arms stop in
    let discr = match List.rev !discrs with
      | [] -> Nil
      | d :: rest -> d ^^ nest 2 (cat (List.map (fun e -> Text "," ^^ group (Line ^^ e)) rest))
    in
    (* aligned to the `match` keyword: the alternatives sit under it even
       when a bracket precedes it on the line *)
    item ~anchor:true (Align (group (kw ^^ nest 2 discr ^^ with_ ^^ head_trail) ^^ arms))
  and parse_let stop t =
    let kw = opener t in
    let lhs = parse_seq (fun x -> x.s = ":=") in
    let assign = expect ":=" in
    let sep = body_sep () in
    let value = parse_seq (fun x -> x.k = Semi || stop x) in
    (match peek () with Some x when x.k = Semi -> advance () | _ -> raise (Bail "let without ;"));
    (* the comments after the `;` lead the body: in front of another `let`
       they get a line of their own, as in the source *)
    let body = parse_seq stop in
    (* aligned to the `let` keyword: Lean anchors the binding at it, so the
       value's continuation lines must be right of it even after `((let` *)
    item ~anchor:true (Align (kw ^^ lhs ^^ assign ^^ group (nest 2 (sep ^^ value)) ^^ Text ";"
                              ^^ HardLine ^^ body))
  and parse_if stop t =
    let kw = opener t in
    let cond = parse_seq (fun x -> x.s = "then") in
    let then_ = expect "then" in
    let trail_t = take_inline_comments () in
    let sep_a = body_sep () in
    let a = parse_seq (fun x -> x.s = "else") in
    let else_ = (match peek () with
        | Some x when x.s = "else" -> advance (); (if x.ws then Line else Nil) ^^ Text x.s
        | _ -> raise (Bail "expected else")) in
    let trail_e = take_inline_comments () in
    let b = match peek () with
      | Some x when x.s = "if" || x.s = "lem_if" -> advance (); Text " " ^^ (parse_if stop x).d
      | _ -> let sep_b = body_sep () in nest 2 (sep_b ^^ parse_seq stop)
    in
    item (group (kw ^^ nest 2 cond ^^ then_ ^^ trail_t ^^ nest 2 (sep_a ^^ a)
                 ^^ else_ ^^ trail_e ^^ b))
  in
  (* the unit itself *)
  let header_doc items =
    (* `name binders : type` — when broken, the binders fill at +4 and the
       result type starts its own line *)
    let rec split before = function
      | [] -> None
      | it :: rest when it.colon && not (List.exists (fun x -> x.colon) rest) ->
        Some (List.rev before, it, rest)
      | it :: rest -> split (it :: before) rest
    in
    match split [] items with
    | Some (before, colon, after) when before <> [] && after <> [] ->
      (* the colon item itself: it may carry a comment, `(x : T) /- c -/ :` *)
      let sep = if (List.hd after).sep = NoSep then Nil else Line in
      group (fill ~n:4 before ^^ sep_doc colon.sep ^^ colon.d ^^ nest 4 (sep ^^ fill ~n:4 after))
    | _ -> group (fill ~n:4 items)
  in
  let first = if n > 0 then Some toks.(0) else None in
  match first with
  | Some t when t.s = "export" ->
    (* export T (names…) *)
    advance ();
    let name = (match peek () with Some x when x.k = Word -> advance (); x.s | _ -> raise (Bail "export")) in
    let op = expect "(" in
    let names = parse_items (fun x -> x.k = Close) in
    let cl = expect ")" in
    if !p <> n then raise (Bail "export tail");
    Text ("export " ^ name) ^^ op ^^ nest 2 (fill names) ^^ cl
  | Some t when t.s = "|" && not (Array.exists (fun x -> x.s = "=>") toks) ->
    (* a constructor line `| C : T` *)
    advance ();
    let bar = opener t in
    let items = parse_items (fun _ -> false) in
    if !p <> n then raise (Bail "constructor tail");
    bar ^^ header_doc items
  | _ ->
    let items = parse_items (fun x -> x.s = ":=" || x.s = "|") in
    let hd = header_doc items in
    (match peek () with
     | None -> hd
     | Some x when x.s = ":=" ->
       let assign = expect ":=" in
       let trail = take_inline_comments () in
       let sep = body_sep () in
       let body = parse_seq (fun _ -> false) in
       if !p <> n then raise (Bail "body tail");
       group (hd ^^ assign ^^ trail ^^ nest 2 (sep ^^ body))
     | Some _ ->
       (* equations `def f : T → U | p => …`, or a lone alternative line *)
       let head_trail, arms = parse_arms (fun _ -> false) in
       if !p <> n then raise (Bail "equations tail");
       if items = [] then arms else hd ^^ head_trail ^^ nest 2 arms)

(* ---------------------------------------------------------------------- *)
(* 5. Driver                                                               *)
(* ---------------------------------------------------------------------- *)

(* A unit left as it was: each line's original text, byte for byte, except
   for the two things the backend does only for this pass, which are undone
   so that the unit is the text that built before the pass:
   - a multi-line comment followed by another token on its line (the
     backend no longer folds the comments inside expressions) is folded
     onto one line, as it was before this pass existed;
   - a line at column 0 that starts with a comment followed by code is the
     backend's marker for "this comment followed a line break in the
     source" (`inline_comments`); it is joined to the line before it, as
     the text was without the marker.
   Nothing else is changed: no re-spacing, no other join. *)
let verbatim_lines (s : string) (ls : line list) : string list =
  let line_text (l : line) =
    let b = Buffer.create 256 in
    let pos = ref l.start in
    let rec go = function
      | [] -> ()
      | (t : tok) :: rest ->
        Buffer.add_string b (String.sub s !pos (t.pos - !pos));
        Buffer.add_string b (if t.k = Comment && has_nl t.s && rest <> [] then fold_comment t.s else t.s);
        pos := t.pos + String.length t.s;
        go rest
    in
    go l.toks;
    Buffer.add_string b (String.sub s !pos (l.stop_ - !pos));
    Buffer.contents b
  in
  let out = ref [] in
  List.iteri (fun i l ->
      let text = line_text l in
      let marker = i > 0 && l.indent = 0
                   && (match l.toks with
                       | t :: (_ :: _ as rest) -> t.k = Comment && List.exists (fun x -> x.k <> Comment) rest
                       | _ -> false) in
      match !out with
      | prev :: rest when marker -> out := (prev ^ " " ^ text) :: rest
      | _ -> out := text :: !out) ls;
  List.rev !out

let debug_bail = Sys.getenv_opt "LEM_LEAN_LAYOUT_DEBUG" <> None

let reflow ?(width = 100) (s : string) : string =
  let toks = lex s in
  let lines = split_lines s toks in
  let units = split_units lines in
  let b = Buffer.create (String.length s + String.length s / 4) in
  let add_line l = Buffer.add_string b l; Buffer.add_char b '\n' in
  let try_layout indent ls =
    let toks = Array.of_list (List.concat_map (fun l -> l.toks) ls) in
    match parse_unit toks with
    | d -> List.iter add_line (render ~width ~indent d)
    | exception Bail why ->
      if debug_bail then
        prerr_endline (Printf.sprintf "lean layout: left as is (%s): %s" why
                         (String.sub s (List.hd ls).start
                            (min 80 ((List.hd ls).stop_ - (List.hd ls).start))));
      List.iter add_line (verbatim_lines s ls)
  in
  List.iter (function
      | Verbatim l -> add_line (String.sub s l.start (l.stop_ - l.start))
      | Decl ls -> try_layout 0 ls
      | Single ls -> try_layout (List.hd ls).indent ls)
    units;
  Buffer.contents b
