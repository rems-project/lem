let r = Ulib.Text.of_latin1
;;

let (|>) x f = f x
;;

type ('a, 'b) union
  = Inl of 'a
  | Inr of 'b
;;

let sum f l =
  List.map f l |>
  List.fold_left (+) 0
;;

let rec repeat (c: char) (i: int): string =
  match i with
    | 0 -> ""
    | m -> Char.escaped c ^ repeat c (m - 1)
;;

let tyvar_size ty =
  Tyvar.to_rope ty |>
  Ulib.Text.to_string |>
  String.length
;;

let name_size n =
  Name.to_rope n |>
  Ulib.Text.to_string |>
  String.length
;;

let path_size p =
  Path.to_name p |>
  name_size
;;

type typ
  = TyWildcard
  | TyVar of Tyvar.t
  | TyConst of Path.t Typed_ast.id
  | TyArrow of typ * typ
  | TyBracketed of typ
  | TyApp of Path.t Typed_ast.id * typ list
  | TyWhitespace of Ast.lex_skip list * typ
  | TyComment of string * typ
;;

let rec ml_comment_size c =
  match c with
    | Ast.Chars cs -> cs |> Ulib.Text.to_string |> String.length
    | Ast.Comment cs -> sum ml_comment_size cs
;;

let whitespace_size ws =
  match ws with
    | Ast.Com c -> ml_comment_size c
    | Ast.Nl -> 1
    | Ast.Ws w -> w |> Ulib.Text.to_string |> String.length
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
      String.length c + typ_size typ
;;

let rec string_of_ml_comment c =
  match c with
    | Ast.Chars cs -> Ulib.Text.to_string cs
    | Ast.Comment cs ->
        cs |>
        List.map string_of_ml_comment |>
        String.concat
;;

let string_of_path p =
  Path.to_name p |>
  Name.to_string
;;

let rec pretty_print_whitespace caret limit ws =
  match ws with
    | Ast.Com c ->
      let sep, caret =
        if caret >= limit - whitespace_size ws then
          let m = min (2 + whitespace_size ws) limit in
          let indent = repeat ' ' m in
            "\n" ^ indent, m
        else
          "", min (caret + whitespace_size ws) limit
      in
        caret, sep ^ string_of_ml_comment c
;;

let rec lift (caret: int) (limit: int) (sep: string) (pp: int -> int -> 'a -> int * string) (l: 'a list) =
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

let progress caret limit size i =
  let s = size i in
    if caret >= limit - s then
      let m = min (2 + s) limit in
      let indent = repeat ' ' m in
        "\n" ^ indent, m
    else
      "", min (caret + s) limit
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
        let sep, caret =
          if caret >= limit - typ_size typ then
            let m = min (2 + typ_size typ) limit in
            let indent = repeat ' ' m in
              "\n" ^ indent, m
          else
            "", min (caret + typ_size typ) limit
        in
        let v' = v |> Tyvar.to_rope |> Ulib.Text.to_string in
          caret, sep ^ v'
      | TyConst c ->
        let sep, caret =
          if caret >= limit - typ_size typ then
            let m = min (2 + typ_size typ) limit in
            let indent = repeat ' ' m in
              "\n" ^ indent, m
          else
            "", min (caret + typ_size typ) limit
        in
        let c' = c.Typed_ast.descr |> Path.to_name |> Name.to_rope |> Ulib.Text.to_string in
          caret, sep ^ c'
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
        let ws_size = whitespace_list_size ws in
        let caret, ws = pretty_print_whitespace_list caret limit ws in
          ws ^ aux caret limit t
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
  let caret, pp = pretty_print_typ 77 80 (TyArrow (TyWildcard, TyWildcard)) in
  let _ = prerr_endline (string_of_int caret), prerr_endline pp in
    ()
;;

type bit
  = ZeroBit
  | OneBit
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
  | Comment of string * term
  | Whitespace of Ast.lex_skip list * term
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
