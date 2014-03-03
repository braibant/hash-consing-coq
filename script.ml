
let name = "./bench_bdd.native"

let exec s =
  Printf.printf "excuting:%s\n%!" s ;
  ignore (Sys.command s)


let test  n =
  exec (Printf.sprintf "%s -pure  -o pure.p.log -p %i" name n);
  exec (Printf.sprintf "%s -ref   -o ref.p.log -p %i" name n);
  exec (Printf.sprintf "%s -smart -o smart.p.log -p %i" name n);
  exec (Printf.sprintf "%s -shallow -o shallow.p.log -p %i" name n);
  exec (Printf.sprintf "%s -refc -o ref-conservative.p.log -p %i" name n)

let _ =
  let i = ref 6 in
  while ! i < 18 do
    test !i;
    i := !i+1;
  done


let test n =
  exec (Printf.sprintf "%s -pure  -o pure.u.log -u %i" name n);
  exec (Printf.sprintf "%s -ref   -o ref.u.log -u %i" name n);
  exec (Printf.sprintf "%s -smart -o smart.u.log -u %i" name n);
  exec (Printf.sprintf "%s -shallow -o shallow.u.log -u %i" name n);
  exec (Printf.sprintf "%s -refc -o ref-conservative.u.log -u %i" name n)

let _ =
  let r = ref 10. in
  while !r < 5000. do
    test (int_of_float !r);
    r := !r *. 1.5
  done;


