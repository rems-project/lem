let r = Ulib.Text.of_latin1
;;

let ($) f x = f x
;;

let (|>) f g = fun x -> g (f x)
;;

type ('a, 'b) union
  = Inl of 'a
  | Inr of 'b
;;

let sum f =
  List.map f |>
  fun l -> List.fold_right (+) l 0
;;

let rec repeat (c: char) (i: int): string =
  match i with
    | 0 -> ""
    | m -> Char.escaped c ^ repeat c (m - 1)
;;

let tyvar_size =
  Tyvar.to_rope |>
  Ulib.Text.to_string |>
  String.length
;;

let name_size =
  Name.to_rope |>
  Ulib.Text.to_string |>
  String.length
;;

let path_size =
  Path.to_name |>
  name_size
;;

type lex_skip
  = Nl
  | Ws of Ulib.Text.t
;;

type ml_comment
  = Chars of Ulib.Text.t
  | Comment of ml_comment list
;;

type typ
  = TyWildcard
  | TyVar of Tyvar.t
  | TyConst of Path.t Typed_ast.id
  | TyArrow of typ * typ
  | TyBracketed of typ
  | TyApp of Path.t Typed_ast.id * typ list
  | TyWhitespace of lex_skip list * typ
  | TyComment of ml_comment * typ
;;

let rec ml_comment_size c =
  match c with
    | Chars cs -> Ulib.Text.to_string |> String.length $ cs
    | Comment cs -> sum ml_comment_size cs
;;

let rec string_of_ml_comment c =
  match c with
    | Chars cs -> Ulib.Text.to_string cs
    | Comment cs ->
        List.map string_of_ml_comment |>
        (fun x -> List.fold_right (^) x "") $
        cs
;;

let whitespace_size ws =
  match ws with
    | Nl -> 1
    | Ws w -> Ulib.Text.to_string |> String.length $ w
;;

let whitespace_list_size ws =
  match ws with
    | [] -> 0
    | [x] -> whitespace_size x
    | _ -> sum whitespace_size ws + 2 * (List.length ws - 1)
;;

let rec typ_size = function
  | TyWildcard -> 1
  | TyVar v -> tyvar_size v
  | TyConst c -> path_size c.Typed_ast.descr
  | TyArrow (left, right) ->
      2 + typ_size left + typ_size right
  | TyBracketed typ ->
      2 + typ_size typ
  | TyApp (path, args) ->
      sum typ_size args + path_size path.Typed_ast.descr
  | TyWhitespace (ws, typ) ->
      sum whitespace_size ws + typ_size typ
  | TyComment (c, typ) ->
      ml_comment_size c + typ_size typ
;;

let string_of_path =
  Path.to_name |>
  Name.to_string
;;

let progress caret limit size i =
  let s = size i in
    if caret >= limit - s then
      let m = min (2 + s) limit in
      let indent = repeat ' ' m in
        "\n" ^ indent, m
    else
      "", min (caret + s) limit
;;

let pretty_print_ml_comment caret limit c =
  let sep, caret = progress caret limit ml_comment_size c in
    caret, sep ^ string_of_ml_comment c
;;

let rec pretty_print_whitespace caret limit w =
  match w with
    | Nl ->
      let _, caret = progress caret limit whitespace_size w in
        caret, "\n"
    | Ws ws ->
      let sep, caret = progress caret limit whitespace_size w in
        caret, sep ^ Ulib.Text.to_string ws
;;

let rec lift (caret: int) (limit: int) (sep: string)
              (pp: int -> int -> 'a -> int * string) (l: 'a list) =
  match l with
    | [] -> caret, ""
    | x::xs ->
      let sep_length = String.length sep in
      let caret, x = pp caret limit x in
      let caret, rest = lift (caret + sep_length) limit sep pp xs in
        caret, x ^ sep ^ rest
;;

let rec pretty_print_whitespace_list caret limit =
  lift caret limit " " pretty_print_whitespace
;;

let pretty_print_path caret limit p =
  let sep, caret = progress caret limit path_size p in
    caret, sep ^ string_of_path p
;;

let pretty_print_typ =
  let rec aux (caret: int) (limit: int) (typ: typ): int * string =
    match typ with
      | TyWildcard ->
        let sep, caret = progress caret limit typ_size typ in
          caret, sep ^ "_"
      | TyVar v ->
        let sep, caret = progress caret limit typ_size typ in
        let v = Tyvar.to_rope |> Ulib.Text.to_string $ v in
          caret, sep ^ v
      | TyConst c ->
        let sep, caret = progress caret limit typ_size typ in
        let c = Path.to_name |> Name.to_rope |> Ulib.Text.to_string $ c.Typed_ast.descr in
          caret, sep ^ c
      | TyArrow (l, r) ->
        let caret, l = aux caret limit l in
        let caret', r = aux (caret + 4) limit r in
          caret', l ^ " -> " ^ r
      | TyBracketed t ->
          let caret, t = aux (caret + 1) limit t in
            caret + 1, "(" ^ t ^ ")"
      | TyApp (l, r) ->
        let caret, l = pretty_print_path caret limit l.Typed_ast.descr in
        let caret, r = aux_list (caret + 1) limit r in
          caret, l ^ " " ^ r
      | TyWhitespace (ws, t) ->
        let caret, ws = pretty_print_whitespace_list caret limit ws in
        let caret, t = aux caret limit t in
          caret, ws ^ t
      | TyComment (c, t) ->
        let caret, c = pretty_print_ml_comment caret limit c in
        let caret, t = aux caret limit t in
          caret, c ^ t
    and aux_list caret limit = lift caret limit " " aux
  in
    aux
;;

let _ =
  let caret, pp = pretty_print_typ 0 80 TyWildcard in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
  let caret, pp = pretty_print_typ 79 80 TyWildcard in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
  let caret, pp = pretty_print_typ 77 80 TyWildcard in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
  let caret, pp = pretty_print_typ 77 80 (TyArrow (TyArrow (TyBracketed TyWildcard, TyWildcard), TyWildcard)) in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
    ()
;;

type bit
  = ZeroBit
  | OneBit
;;

let string_of_bit = function
  | ZeroBit -> "Zero"
  | OneBit -> "One"
;;

type vector_literal_type
  = HexVector
  | BinaryVector
;;

type collection_type
  = SetCollection
  | ListCollection
  | TupleCollection
;;

type comprehension_type
  = SetComprehension
  | ListComprehension
;;

type literal
  = LBoolean of bool
  | LBit of bit
  (* bits for use in vectors *)
  | LInt of int
  | LString of string
  | LUnit
  (* should be somehow made a constant, not a literal *)
  | LVector of vector_literal_type * int * int
  (* first int is the integer to be printed, second is the length of the vector *)
  (* for truncation/padding purposes *)
  | LUndefined of string
  (* string is the justification for the use of undefined in the backend *)
  | LCollection of collection_type * term list
and term
  = Var of Name.t
  | Const of (Name.t, literal) union
  | Bracketed of term
  | Explicit of term * typ
  | Comment of ml_comment * term
  | Whitespace of lex_skip list * term
  | Infix of term * term * term
  | App of term * term
  | Fun of term list * term
  | Match of term * (term * term) list
  | Conditional of term * term * term
  | Comprehension of comprehension_type * term * Typed_ast.quant_binding list * term
  | Record of string * term list
  (* XXX: change to something more appropriate when I figure out what, exactly,
     that more appropriate thing is!
  *)
  | Recup of term * string * term
  (* XXX: change to something more appropriate when I figure out what, exactly,
     that more appropriate thing is!
  *)
  | Do of Typed_ast.mod_descr Typed_ast.id * (term * term) list
;;

let rec term_size t =
  match t with
    | Var v -> name_size v
    | Const c ->
      (match c with
        | Inl n -> name_size n
        | Inr l -> literal_size l)
    | Bracketed t -> 2 + term_size t
    | Explicit (t, typ) -> 2 + term_size t + typ_size typ
and literal_size l =
  match l with
    | LBoolean b -> string_of_bool |> String.length $ b
    | LBit b -> string_of_bit |> String.length $ b
    | LInt i -> string_of_int |> String.length $ i
    | LString s -> String.length s
    | LUnit -> 2
    | LVector (_, _, l) -> 2 + l
    | LUndefined c -> 9 + String.length c
    | LCollection (_, ts) ->
      match ts with
        | [] -> 2
        | [x] -> term_size x + 2
        | _ ->
          let ts_size = sum term_size ts in
            2 + ts_size + ((List.length ts - 1) * 2)
;;

let pretty_print_term =
  let rec aux_term caret limit t =
    match t with
      | Var v ->
        let sep, caret = progress caret limit term_size t in
        let v = Name.to_string v in
          caret, sep ^ v
  and aux_literal caret limit l =
    match l with
      | LBoolean b ->
        let sep, caret = progress caret limit literal_size l in
          caret, sep ^ string_of_bool b
  in
    aux_term
;;

let _ =
  let caret, pp = pretty_print_term 0 80 (Const (Inr (LBoolean true))) in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
  let caret, pp = pretty_print_term 79 80 (Const (Inr (LBoolean false))) in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
  let caret, pp = pretty_print_term 0 80 (Explicit (Const (Inr (LUndefined "foo")), TyArrow (TyWildcard, TyWildcard))) in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
    ()
;;