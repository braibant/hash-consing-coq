open Helpers_common
open BinNums
open Datatypes
open Weakhtbl

type bdd =
| T of tag | F of tag | N of positive * bdd * bdd * tag

let bdd_tag = function T t | F t -> t | N (_, _, _, t) -> t

module HCbdd = Hashcons.Make(struct
  type t = bdd

  let equal x y =
    match x, y with
    | T _, T _ -> true
    | F _, F _ -> true
    | N (v, t, f, _), N (v', t', f', _) ->
	t == t' && f == f' && v = v'
    | _, _ -> false

  let hash = function
    | T _ -> 3
    | F _ -> 5
    | N (v, t, f, _) -> Hashcons.combine3 7
	  (Helpers_common.N.int_of_positive v)
	  (tag_hash (bdd_tag t)) (tag_hash (bdd_tag f))

  let tag tag = function
    | T _ -> T (create_tag tag)
    | F _ -> F (create_tag tag)
    | N (v, t, f, _) -> N (v, t, f, create_tag tag)
end)

(* let _ = at_exit (fun () -> print_stats "hc" (HCbdd.stats ()));; *)

let hT = HCbdd.hashcons (T Weakhtbl.dummy_tag)
let hF = HCbdd.hashcons (F Weakhtbl.dummy_tag)
let hN (v, t, f) = HCbdd.hashcons (N (v, t, f, Weakhtbl.dummy_tag))

let bdd_match fT fF fN t =
  match t with
  | T _ -> fT ()
  | F _ -> fF ()
  | N (v, t, f, _) -> fN v t f

module WHT = Weakhtbl.Make(struct type t = bdd let tag = bdd_tag end)

let bdd_memo : bdd memoizer = { memo = WHT.memoize_rec }
