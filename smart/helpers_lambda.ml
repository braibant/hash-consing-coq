open Helpers_common
open BinNums
open Datatypes

type term =
| Var of coq_N * Weakhtbl.tag
| App of term * term * Weakhtbl.tag
| Abs of term * Weakhtbl.tag

let term_tag = function Var (_, t) | App (_, _, t) | Abs (_, t) -> t

module HCterm = Hashcons.Make(struct
  type t = term

  let equal x y =
    match x, y with
    | Var (n, _), Var (m, _) -> n = m
    | App (a, b, _), App (a', b', _) -> a == a' && b == b'
    | Abs (a, _), Abs (a', _) -> a == a'
    | _, _ -> false

  let hash = function
    | Var (n, _) -> Hashcons.combine 3 (Hashtbl.hash n)
    | App (a, b, _) ->
	Hashcons.combine2 5
	  (Weakhtbl.tag_hash (term_tag a)) (Weakhtbl.tag_hash (term_tag b))
    | Abs (t, _) -> Hashcons.combine 7 (Weakhtbl.tag_hash (term_tag t))

  let tag tag = function
    | Var (n, _) -> Var (n, Weakhtbl.create_tag tag)
    | App (a, b, _) ->
	App (a, b, Weakhtbl.create_tag tag)
    | Abs (t, _) ->
	Abs (t, Weakhtbl.create_tag tag)
end)

let _ = at_exit (fun () -> print_stats "hc" (HCterm.stats ()));;

let hVar n = HCterm.hashcons (Var (n, Weakhtbl.dummy_tag))
let hApp (a,b) = HCterm.hashcons (App (a, b, Weakhtbl.dummy_tag))
let hAbs a = HCterm.hashcons (Abs (a, Weakhtbl.dummy_tag))

let term_match fVar fApp fAbs t =
  match t with
  | Var (n, _) -> fVar n
  | App (a, b, _) -> fApp a b
  | Abs (a, _) -> fAbs a

module WHT = Weakhtbl.Make(struct
  type t = term
  let tag = term_tag
end)

let term_memo : term memoizer = { memo = WHT.memoize_rec }
