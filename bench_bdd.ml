let time f x =
  let u = Unix.gettimeofday () in
  let r = f x  in
  r, Unix.gettimeofday () -. u


type t =
| Var of string
| Not of t
| And of t * t
| Or  of t * t
| Xor of t * t
| Iff of t * t
| True
| False

let rec size = function
  | Not t -> size t
  | And (t1,t2) | Xor (t1,t2) | Or (t1,t2) | Iff (t1,t2) -> size t1 + size t2
  | _ -> 1

let imp a b = Or (Not a, b)

module Urquahrt = struct
(* x1 <-> (x2 <-> ... (xn <-> (x1 ... <-> xn))) *)

  let main n =
    let iff a b = Iff (a,b)  in
    let var s = Var (string_of_int s) in
    let rec aux k =
    if k < 2*n - 1
    then iff (var (k mod n)) (aux (k+1))
    else var (n-1)
    in aux 0
end

module Pigeon = struct

  let occ i j = Var ("occ_" ^ string_of_int i ^ "_" ^ string_of_int j)

  let (&&) p1 p2 = match p1, p2 with
    | True, p
    | p, True -> p
    | _ -> And (p1, p2)

  let (||) p1 p2 = match p1, p2 with
    | False, p
    | p, False -> p
    | _ -> Or (p1, p2)

  let ands i j f =
    let rec mk k = if k > j then True else (f k) && (mk (k+1)) in
    mk i

  let ors i j f =
    let rec mk k = if k > j then False else (f k) || (mk (k+1)) in
    mk i

  let left n = ands 1 (n+1) (fun p -> ors 1 n (fun j -> occ p j))

  let right n =
    ors 1 n (fun h ->
      ors 1 (n+1) (fun p1 ->
	ors (p1+1) (n+1) (fun p2 -> (occ p1 h) && (occ p2 h))))

  let main n = imp (left n) (right n)
end

let fresh () =
  let n = ref 1 in
  let vars = Hashtbl.create 17 in
  fun s ->
    try Hashtbl.find vars s
    with | Not_found ->
      let k = !n in
      Hashtbl.add vars s k;
      incr n;
      k

(* Coq's [positive] type and some of its operations, excerpt from CompCert *)
module Positive = struct

  open Datatypes
  open BinNums
  open BinPos

  type t = positive = Coq_xI of t | Coq_xO of t | Coq_xH

  let rec of_int n =
    if n = 0 then assert false else
      if n = 1 then Coq_xH else
	if n land 1 = 0
	then Coq_xO (of_int (n lsr 1))
	else Coq_xI (of_int (n lsr 1))

  let rec to_int n =
    match n with
    | Coq_xI n -> 2*(to_int n) + 1
    | Coq_xO n -> 2*(to_int n)
    | _ -> 1
end

(* Coq's [nat] type, excerpt from CompCert *)
module Nat = struct

  open Datatypes
  open BinNums
  open BinPos

  type t = nat = O | S of t

  let rec of_int n =
    assert (n >= 0);
    if n = 0 then O else S (of_int (pred n))

end

module Smart = struct
  open Smart_bdd

  (* builds a bdd out of a formula *)
  let mk f =
    let var = fresh () in
    let rec mk = function
      | Var s -> bdd_var (Positive.of_int (var s))
      | Not x -> bdd_not (mk x)
      | And (x,y) -> let x = mk x in let y = mk y in  bdd_and x y
      | Or  (x,y) -> let x = mk x in let y = mk y in  bdd_or x y
      | Xor (x,y) -> let x = mk x in let y = mk y in  bdd_xor x y
      | Iff (x,y) -> let x = mk x in let y = mk y in  bdd_not (bdd_xor x y )
      | True -> bdd_true
      | False -> bdd_false
    in
    mk f

  let is_sat b = b != bdd_false
  let is_tauto  b = b ==  bdd_true
end

module Pure = struct
  (* builds a bdd out of a formula *)

  type bdd = Pure_bdd.state
  type 'a m = bdd ->  ('a * bdd) option

  let (>>) (x: 'a m) (f: 'a -> 'b m) = fun bdd ->
    begin match x bdd with
    | None -> assert false
    | Some (x,bdd) -> f x bdd
    end

  let mk f  =
    let var = fresh () in
    let open Pure_bdd in
    let rec depth = Nat.S depth in
    let rec mk x : 'a m =
      match x with
      | Var s ->
	fun bdd -> Some (mk_var (Positive.of_int (var s)) bdd)
      | Not x ->
	(mk x) >> (mk_not depth)
      | And (x,y) ->
	(mk x) >> (fun x ->
	  (mk y) >> (fun y ->
	    mk_and depth x y
	   ))
      | Or  (x,y) ->
	(mk x) >> (fun x ->
	  (mk y) >> (fun y ->
	    mk_or depth x y
	   ))
      | Xor (x,y) ->
	(mk x) >> (fun x ->
	  (mk y) >> (fun y ->
	    mk_xor depth x y
	   ))
      | Iff (x,y) ->
	(mk x) >> (fun x ->
	  (mk y) >> (fun y ->
	    (mk_xor depth x y) >> (mk_not depth)
	   ))
      | True -> fun bdd -> Some (mk_true bdd)
      | False -> fun bdd -> Some (mk_false bdd)
    in
    mk f empty

  let is_sat b = b != Pure_bdd.F
  let is_tauto b = b = Pure_bdd.T

  open Pure_bdd
  let rec print bdd fmt expr = match expr with
    | T -> Printf.fprintf fmt "T"
    | F -> Printf.fprintf fmt "F"
    | N p ->
      let Some ((l,v),h) = Common.PMap.find p bdd.to_hashcons.graph in
      Printf.fprintf fmt "%i N  (%i,%a,%a)"
	(Positive.to_int p)
	(Positive.to_int v)
	(print bdd) l
	(print bdd) h
end

module Reference = struct
  (* builds a bdd out of a formula *)
  open Bdd


  let mk f =
    let var = fresh () in
    let rec nb_var = function
      | Var s ->
	var s
      | Not x ->
	nb_var x
      | And (x,y) ->
	max (nb_var x) (nb_var y)
      | Or (x,y) ->
	max (nb_var x) (nb_var y)
      | Xor (x,y) ->
	max (nb_var x) (nb_var y)
      | Iff (x,y) ->
	max (nb_var x) (nb_var y)
      | True -> 0
      | False -> 0
    in

    let (_,t) = time set_max_var (nb_var f) in
    (* Printf.printf "reference init %fs\n%!" t; *)

    let rec mk  x=
      match x with
      | Var s ->
	mk_var (var s)
      | Not x ->
	mk_not (mk x)
      | And (x,y) ->
	mk_and (mk x) (mk y)
      | Or  (x,y) ->
	mk_or (mk x) (mk y)
      | Xor (x,y) ->
	mk_xor (mk x) (mk y)
      | Iff (x,y) ->
	mk_iff (mk x) (mk y)
     | True -> one
      | False -> zero
    in
    mk f

  let is_sat = is_sat
  let is_tauto = tautology
end

module ReferenceConservative = struct
  (* builds a bdd out of a formula *)
  open Bdd_conservative


  let mk f =
    let var = fresh () in
    let rec nb_var = function
      | Var s ->
	var s
      | Not x ->
	nb_var x
      | And (x,y) ->
	max (nb_var x) (nb_var y)
      | Or (x,y) ->
	max (nb_var x) (nb_var y)
      | Xor (x,y) ->
	max (nb_var x) (nb_var y)
      | Iff (x,y) ->
	max (nb_var x) (nb_var y)
      | True -> 0
      | False -> 0
    in

    let (_,t) = time set_max_var (nb_var f) in
    (* Printf.printf "reference init %fs\n%!" t; *)

    let rec mk  x=
      match x with
      | Var s ->
	mk_var (var s)
      | Not x ->
	mk_not (mk x)
      | And (x,y) ->
	mk_and (mk x) (mk y)
      | Or  (x,y) ->
	mk_or (mk x) (mk y)
      | Xor (x,y) ->
	mk_xor (mk x) (mk y)
      | Iff (x,y) ->
	mk_iff (mk x) (mk y)
     | True -> one
      | False -> zero
    in
    mk f

  let is_sat = is_sat
  let is_tauto = tautology
end

module Shallow = struct
  open Shallow_bdd

  type 'a m = state ->  ('a * state)

  let (>>) (x: 'a m) (f: 'a -> 'b m) = fun st ->
    let (r,st) = x st in
    f r st

  let mk f  =
    let var = fresh () in
    let rec mk x : 'a m =
      match x with
      | Var s -> mk_var (Positive.of_int (var s))
      | Not x -> mk x >> mk_not
      | And (x,y) ->
	mk x >> fun x ->
	mk y >> fun y ->
	  mk_and x y
      | Or (x,y) ->
	mk x >> fun x ->
	mk y >> fun y ->
	  mk_or x y
      | Xor (x,y) ->
	mk x >> fun x ->
	mk y >> fun y ->
	  mk_xor x y
      | Iff (x,y) ->
	mk x >> fun x ->
	mk y >> fun y ->
	  mk_xor x y >> mk_not
      | True ->  mk_true
      | False -> mk_false
    in
    mk f empty

  let is_sat (HC (b,_)) = b != Shallow_bdd.F
  let is_tauto (HC (b,_)) = b = Shallow_bdd.T

end
let _ = Gc.set ({(Gc.get ()) with
  Gc.minor_heap_size = (1 lsl 20) ;
  Gc.major_heap_increment = (1 lsl 24)})


type mode = Ref | RefC | Smart | Pure | Shallow
let mode = ref None
let set_mode s () = mode := Some s

let out = ref None
let set_output o = out := Some o

let log msg =
  match !out with
  | None -> Printf.printf "%s\n" msg
  | Some o -> let o = open_out_gen [Open_creat; Open_append] 0o777 o in
	      Printf.fprintf o "%s\n" msg;
	      close_out o

let test msg f =
  match !mode with
  | None -> invalid_arg "Please select the implementation to test"
  | Some RefC ->
    let f,r  = time ReferenceConservative.mk f in
    assert (ReferenceConservative.is_tauto f);
    log (Printf.sprintf "ref  \t%.20s\t%.5f" msg r)
  | Some Ref ->
    let f,r  = time Reference.mk f in
    assert (Reference.is_tauto f);
    log (Printf.sprintf "ref  \t%.20s\t%.5f" msg r)
  | Some Pure ->
    let f,r  = time Pure.mk f in
    assert (match f with None -> false | Some (f,_) -> Pure.is_tauto f);
    log (Printf.sprintf "pure \t%.20s\t%.5f" msg r)
  | Some Smart ->
    let f,r  = time Smart.mk f in
    assert (Smart.is_tauto f);
    log (Printf.sprintf "smart\t%.20s\t%.5f" msg r)
  | Some Shallow ->
    let (f,_),r  = time Shallow.mk f in
    assert (Shallow.is_tauto f);
    log (Printf.sprintf "shallow\t%.20s\t%.5f" msg r)

let p n = test (Printf.sprintf "pigeon\t%.5i" n) (Pigeon.main n)
let u n = test (Printf.sprintf "urquahrt\t%.5i" n) (Urquahrt.main n)

let args =
  let open Arg in
  [
    "-p", Int p, "Pigeonhole formula ([n] pigeons)";
    "-u", Int u, "Urquahrt formula (size [n])";
    "-ref", Unit (set_mode Ref), "Reference implementation";
    "-refc", Unit (set_mode RefC), "Reference (conservative) implementation";
    "-smart", Unit (set_mode Smart), "Smart implementation";
    "-pure", Unit (set_mode Pure), "Pure implementation";
    "-shallow", Unit (set_mode Shallow), "Shallow implementation";
    "-o", String (set_output), "Set output file";
  ]

let _ = Arg.parse args (fun _ -> ()) ""


(*
  Local Variables:
  compile-command: "ocamlbuild -lib unix -I bdd-reference -I extracted -I smart bench_bdd.native"
  End:
*)
