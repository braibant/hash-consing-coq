(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Binary Decision Diagrams (BDDs) *)

(** Number of variables *)

val get_max_var : unit -> int
  (** Returns the number of variables [max_var]. 
      Default value is 0, which means that bdds cannot be created
      until the module is initialized using [set_max_var]. *)

type variable = int 
    (** A variable is an integer, ranging from 1 to [max_var]. *)

val set_max_var : ?size:int -> int -> unit
  (** Sets the number [max_var] of variables.
      Additionally, the size of the internal nodes table for each variable
      can be specified. Each table has a default size (7001) and is 
      resized when necessary (i.e. when too many collisions occur).
      IMPORTANT NOTE: bdds created before [set_max_var] should not be used
      anymore. *) 


(** The abstract type of BDD nodes *)

type t

(** View *)

type view = Zero | One | Node of variable * t (*low*) * t (*high*)

val view : t -> view
  (** Displays a bdd as a tree. *)

(** Accessors *)

val var : t -> variable
    (** The root variable of a bdd.
	Convention: [Zero] and [One] have variable [max_var+1] *)

val low : t -> t
val high : t -> t
    (** The low and high parts of a bdd, respectively.
	[low] and [high] raise [Invalid_argument] on [Zero] and [One]. *)

(** Constructors *)

val zero : t
val one : t

val make : variable -> low:t -> high:t -> t
  (** Builds a bdd node. 
      Raises [Invalid_argument] is the variable is out of [1..max_var]. *)

val mk_var : variable -> t
  (** Builds the bdd reduced to a single variable. *)

val mk_not : t -> t
val mk_and : t -> t -> t
val mk_or : t -> t -> t
val mk_xor : t -> t -> t
val mk_imp : t -> t -> t
val mk_iff : t -> t -> t
  (** Builds bdds for negation, conjunction, disjunction and implication. *)

(** Generic binary operator constructor *)

val apply : (bool -> bool -> bool) -> t -> t -> t

(** Propositional formulas *)

type formula = 
  | Ffalse 
  | Ftrue 
  | Fvar of variable 
  | Fand of formula * formula
  | For  of formula * formula
  | Fimp of formula * formula
  | Fiff of formula * formula
  | Fnot of formula

val build : formula -> t
  (** Builds a bdd from a propositional formula [f].
      Raises [Invalid_argument] if [f] contains a variable out of 
      [1..max_var]. *)

(** Satisfiability *)

val is_sat : t -> bool 
  (** Checks if a bdd is satisfiable i.e. different from [zero] *)

val tautology : t -> bool
  (** Checks if a bdd is a tautology i.e. equal to [one] *)

val count_sat : t -> Int64.t
  (** Counts the number of different ways to satisfy a bdd. *)

val any_sat : t -> (variable * bool) list
  (** Returns one truth assignment which satisfies a bdd, if any.
      The result is chosen deterministically.
      Raises [Not_found] if the bdd is [zero] *)

val random_sat : t -> (variable * bool) list
  (** Returns one truth assignment which satisfies a bdd, if any.
      The result is chosen randomly.
      Raises [Not_found] if the bdd is [zero] *)

val all_sat : t -> (variable * bool) list list
  (** Returns all truth assignments which satisfy a bdd [b]. *)

(** Pretty printer *)

val print_to_dot : t -> file:string -> unit

val display : t -> unit
  (** displays the given bdd using a shell command "dot -Tps <file> | gv -" *)

(** Stats *)

val stats : unit -> (int * int * int * int * int * int) array
  (** Return statistics on the internal nodes tables (one for each variable).
      The numbers are, in order:
      table length, number of entries, sum of bucket lengths,
      smallest bucket length, median bucket length, biggest bucket length. *)
