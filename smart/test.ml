(* Coq's [nat] type, excerpt from CompCert *)
module Nat = struct
  open Datatypes
  type t = nat = O | S of t
  let rec of_int n =
    assert (n >= 0);
    if n = 0 then O else S (of_int (pred n))
  let rec to_int = function
    | O -> 0
    | S k -> 1+to_int k
end

type t = {time: float; alloc: float}

let stat f x =
  let a = Gc.allocated_bytes ()  in
  let u = Unix.gettimeofday () in
  let r = f x  in
  let time = Unix.gettimeofday () -. u in
  let alloc = Gc.allocated_bytes () -. a  in
  r, {time; alloc}

let mean l = List.fold_left (+.) 0. l /. (float (List.length l))

let gmean l = exp (mean (List.map log l))

let median l =
  let v = Array.of_list l in
  Array.sort compare v;
  let n = Array.length v in
  (v.((n - 1) / 2) +. v.(n / 2)) /. 2.

let sample n (f: unit -> 'a) : 'a list =
  let rec aux acc = function 0 -> List.rev acc
    | n -> aux (f () :: acc) (pred n)
  in
  aux [] n

let rec random_list k = function
  | 0 -> []
  | n -> Nat.of_int (Random.int k) :: random_list k (pred n)

let test f =
  let l = List.map (Nat.of_int) [0;3;5;2;4;1] in
  let r,s =  (stat f l) in
  let _ = match r with | None -> Printf.printf "error\n"
    | Some r -> List.iter (fun x -> Printf.printf "%i;" (Nat.to_int x)) r ; print_newline ()
  in
  let top () = let open Gc in Gc.minor (); let s = Gc.stat () in s.top_heap_words in 
  Printf.printf "time: %f s\t alloc: %.0f kb\t top: %i\n" s.time (s.alloc /. 1000.) (top ())

let test_ref () = test (Reference.quicksort')
let test_smart () = test (Smart_lambda.quicksort' Helpers_common.magic_fuel)

let args =
  let open Arg in
  ["-ref", Unit (test_ref), " ";
   "-smart", Unit (test_smart), " "]

let _ = Arg.parse args (fun _ -> ()) ""

 (*
  let samples = Array.init 10 (fun i -> sample 10 (fun () -> random_list 20 i))  in
  let n = 6 in
  for i = 5 to n do
    let l = samples.(i) in
    let res = List.map (fun x -> snd (stat Reference.quicksort x)) l in
    let time = List.map (fun x -> x.time) res in
    let space = List.map (fun x -> x.alloc) res in
    Printf.printf "%i (time):  mean %10fs\tmedian %10fs\tgmean %10fs\n%!" i (mean time) (median time) (gmean time);
    Printf.printf "%i (space): mean %10.0fkw\tmedian %10.0fkw\tgmean %10.0fkw\n%!" i (mean space) (median space) (gmean space)
  done;


  for i = 5 to n do
    let l = samples.(i) in
    let res = List.map (fun x -> snd (stat Smart_common.quicksort x)) l in
    let time = List.map (fun x -> x.time) res in
    let space = List.map (fun x -> x.alloc) res in
    Printf.printf "%i (time):  mean %10fs\tmedian %10fs\tgmean %10fs\n%!" i (mean time) (median time) (gmean time);
    Printf.printf "%i (space): mean %10.0fkw\tmedian %10.0fkw\tgmean %10.0fkw\n%!" i (mean space) (median space) (gmean space)
  done
 *)
