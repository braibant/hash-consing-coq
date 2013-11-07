open Datatypes
open BinNums

module N = struct
  let rec int_of_positive = function
    | Coq_xH -> 1
    | Coq_xI p -> 2*int_of_positive p + 1
    | Coq_xO p -> 2*int_of_positive p

  let rec positive_of_int = function
    | 1 -> Coq_xH
    | p when p mod 2 = 1 -> Coq_xI (positive_of_int (p/2))
    | p -> Coq_xO (positive_of_int (p/2))

  let to_int n =
    match n with
    | N0 -> 0
    | Npos p -> int_of_positive p

  let of_int = function 0 -> N0 | p -> Npos (positive_of_int p)
end

let print_stats msg (tl, ne, sbl, minbl, medbl, bigbl) =
  Printf.printf "%s\n" msg;
  Printf.printf "table lengt   h        %i\n" tl;
  Printf.printf "number of entries      %i\n" ne;
  Printf.printf "sum of bucket length   %i\n" sbl;
  Printf.printf "smallest bucket length %i\n" minbl;
  Printf.printf "median bucket length   %i\n" medbl;
  Printf.printf "biggest bucket length  %i\n"  bigbl

type 'key memoizer =
    { memo : 'a. int -> (('key -> 'a) -> ('key -> 'a)) -> ('key -> 'a) }

module NHT =
  Hashtbl.Make (struct
    type t = coq_N
    let equal = (=)
    let hash = N.to_int
  end)

let memoizer_N =
  { memo = fun n f ->
    let h = NHT.create n in
    let rec aux x =
      try NHT.find h x
      with Not_found ->
	let r = f aux x in
	NHT.replace h x r;
	r
    in aux }

let memo m f = m.memo 5 (fun _ -> f)

let memo_rec m f = m.memo 5 (fun frec x -> f x (fun y _ -> frec y))

let rec magic_fuel = S magic_fuel

let memo_fuel m f fuel =
  if fuel == magic_fuel then
    m.memo 5 (fun frec x -> f x frec)
  else
    let rec fuel_fix n x =
      match n with
      | O -> None
      | S n -> f x (fuel_fix n)
    in
    fuel_fix fuel
