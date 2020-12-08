(**************************************************************************)
(*                                                                        *)
(*  GOSPEL -- A Specification Language for OCaml                          *)
(*                                                                        *)
(*  Copyright (c) 2018- The VOCaL Project                                 *)
(*                                                                        *)
(*  This software is free software, distributed under the MIT license     *)
(*  (as described in file LICENSE enclosed).                              *)
(**************************************************************************)

(* This file contains the GOSPEL standard library.
   It is automatically opened.

   The following are built-in in GOSPEL:

   type unit
   type string
   type float
   type bool
   type integer

   type 'a option
   function None: 'a option
   function Some (x: 'a) : 'a option

   type 'a list
   function ([]): 'a list
   function (::) (x: 'a) (l: 'a list) : 'a list

   predicate (=) (x y: 'a)
*)

(** Arithmetic

   The type [integer] is built-in. This is the type of arbitrary precision integers,
   not to be confused with OCaml's type [int] (machine integers).

   There is a coercion from type [int] to type [integer], so that GOSPEL specifications
   can be written using type [integer] only, and yet use OCaml's variables of type [int].
*)

(*@ function (+)   (x y: integer) : integer *)
(*@ function (-)   (x y: integer) : integer *)
(*@ function ( * ) (x y: integer) : integer *)
(*@ function (/)   (x y: integer) : integer *)
(*@ function mod   (x y: integer) : integer *)
(*@ function (-_)  (x: integer) : integer *)
(*@ predicate (>)  (x y: integer) *)
(*@ predicate (>=) (x y: integer) *)
(*@ predicate (<)  (x y: integer) *)
(*@ predicate (<=) (x y: integer) *)

type int

(*@ function integer_of_int (x: int) : integer *)
(*@ coercion *)

(*@ function abs (x:integer) : integer = if x >= 0 then x else -x *)

(*@ function min (x y : integer) : integer
    = if x <= y then x else y *)

(*@ function max (x y : integer) : integer
    = if x <= y then y else x *)

(*@ function succ (x: integer) : integer = x + 1 *)
(*@ function pred (x: integer) : integer = x - 1 *)

(*@ function max_int : integer *)
(*@ function min_int : integer *)

(** {1 Couples} *)

(*@ function fst (p: 'a * 'b) : 'a *)
(** [fst (x, y)] is [x]. *)

(*@ function snd (p: 'a * 'b) : 'b *)
(** [snd (x, y)] is [y]. *)

(** {1 References} *)

type 'a ref
(** The type for references. *)

(*@ function (!_) (r: 'a ref) : 'a *)
(** Reference content access operator. *)

(*@ function ref (x: 'a) : 'a ref *)
(** Reference creation. *)

(** {1 Sequences} *)

module Seq : sig
  type 'a t
  (** The type for finite sequences. *)

  (*@ predicate equal (x y: 'a t) *)
  (** Equality predicate over sequences. *)

  (*@ function length (s: 'a t): integer *)
  (** [length s] is the length of the sequence [s]. *)

  (*@ function empty : 'a t *)
  (** [empty] is the empty sequence. *)

  (*@ function return (x: 'a) : 'a t *)
  (** [return x] is the sequence containing only [x]. *)

  (*@ function singleton (x: 'a) : 'a t *)
  (** [singleton] is an alias for {!return}. *)

  (*@ function cons (x: 'a) (s: 'a t): 'a t *)
  (** [cons x s] is the sequence containing the element [x] followed by the
      sequence [s]. *)

  (*@ function append (x y: 'a t) : 'a t *)
  (** [append x y] is the sequence [x] followed by the sequence [y]. *)

  (*@ function (++) (x y: 'a t) : 'a t *)
  (** [x ++ y] is [append x y]. *)

  (*@ function map (f: 'a -> 'b) (s: 'a t) : 'b t *)
  (** [map f s] is a sequence whose elements are the elements of [s],
      transformed by [f]. *)

  (*@ function filter (f: 'a -> bool) (s: 'a t) : 'a t *)
  (** [filter f s] is a sequence whose elements are the elements of [s], that
      satisfy [f]. *)

  (*@ function filter_map (f: 'a -> 'b option) (s: 'a t) : 'b t *)
  (** [filter_map f s] is a sequence whose elements are the elements of [s],
      transformed by [f]. An element [x] is dropped whenever [f x] is [None]. *)

  (*@ function get (s: 'a seq) (i: integer) : 'a *)
  (** [get s i] is the [i]th element of the sequence [s]. *)

  (*@ function ([_]) (s: 'a seq) (i:integer): 'a *)
  (** [s[i]] is an alias for [get s i]. *)

  (*@ function ([_.._]) (s: 'a seq) (i1: integer) (i2: integer): 'a seq *)
  (*@ function ([_..]) (s: 'a seq) (i: integer): 'a seq *)
  (*@ function ([.._]) (s: 'a seq) (i: integer): 'a seq *)

  (*@ function create (n: integer) (f: integer -> 'a) : 'a seq *)

  (*@ function ([<-]) (s: 'a seq) (i: integer) (x: 'a): 'a seq *)

  (*@ function snoc (s: 'a seq) (x: 'a): 'a seq *)

  (*@ predicate mem (s: 'a seq) (x: 'a) *)

  (*@ predicate distinct (s: 'a seq) *)

  (*@ function rev (s: 'a seq) : 'a seq *)

  (*@ function rec fold_left (f: 'a -> 'b -> 'a) (acc: 'a) (s: 'b seq) : 'a *)

  (*@ function rec fold_right (f: 'a -> 'b -> 'b) (s: 'a seq) (acc: 'b) : 'b *)

  (*@ function hd (s: 'a seq) : 'a *)

  (*@ function tl (s: 'a seq) : 'a seq *)

  (* Sorted sequences of int values *)
  (*@ predicate sorted_sub (s: int seq) (l u: integer) =
        forall i1 i2. l <= i1 <= i2 < u -> s[i1] <= s[i2] *)

  (*@ predicate sorted (s: int seq) =
        sorted_sub s 0 (length s) *)
end

module SeqPerm : sig

  (*@ function occ (s1: 'a seq) (v: 'a) (l u: integer) : integer *)

  (*@ axiom occ_base: forall s1 v l u.
        u <= l -> occ s1 v l u = 0 *)

  (*@ axiom occ_ind: forall s1 v l u. 0 <= l <= v < u <= length s1 ->
        occ s1 v l u = (if v = s1[l] then 1 else 0) + occ s1 v (l+1) u *)

  (*@ predicate permut (s1 s2: 'a seq) (l u: integer) =
        length s1 = length s2 &&
        forall x. occ x s1 l u = occ x s2 l u *)

  (*@ predicate permut_all (s1 s2: 'a seq) =
        permut s1 s2 0 (length s1) *)

end

(** Lists

     Type 'a list, [] and (::) constructors are built-in *)

(*@ function seq_of_list (l: 'a list): 'a seq *)
(*@ coercion *)

(** Arrays *)

type 'a array
(*@ ephemeral *)
(*@ mutable model contents: 'a seq *)
(*@ model array_length: integer *)
(*@ invariant array_length = length contents *)

(*@ function elts (a: 'a array): 'a seq = a.contents *)
(*@ coercion *)

module Array : sig

  (* OCaml-like syntax a.(i) is mapped to Array.([_]) *)
  (*@ function ([_]) (a: 'a array) (i: integer) : 'a = Seq.get a i *)

  (*@ function length (a: 'a array) : integer = Seq.len a *)

end

module ArrayPermut : sig

  (*@ predicate permut_sub (a b: 'a array) (i j: integer) *)
  (*@ predicate permut_all (a b: 'a array) *)

end

(** Other OCaml built-in stuff *)

exception Not_found
exception Invalid_argument of string

module Sys : sig

  (*@ function word_size : integer *)

  (*@ function int_size : integer *)

  (*@ function big_endian : bool *)

  (*@ function max_string_length : integer *)

  (*@ function max_array_length : integer *)

end

module Order : sig

  (*@ predicate is_pre_order (cmp: 'a -> 'a -> int) =
      (forall x. cmp x x = 0) /\
      (forall x y. cmp x y <= 0 <-> cmp y x >= 0) /\
      (forall x y z.
         (cmp x y <= 0 -> cmp y z <= 0 -> cmp x z <= 0) /\
         (cmp x y <= 0 -> cmp y z <  0 -> cmp x z <  0) /\
         (cmp x y <  0 -> cmp y z <= 0 -> cmp x z <  0) /\
         (cmp x y <  0 -> cmp y z <  0 -> cmp x z <  0)) *)

end

module Bag : sig
  (*@ type 'a t *)
  (** The type for finite sets. *)

  (*@ function occurences (x: 'a) (b: 'a t): integer *)
  (** [occurences x b] is the number of occurences of [x] in [s]. *)

  (*@ predicate equal (s s': 'a t) *)
  (** [equal s s'] is [s = s']. *)

  (*@ function empty : 'a t *)
  (** [empty] is [∅]. *)

  (*@ predicate is_empty (s: 'a t) *)
  (** [is_empty s] is [s = ∅]. *)

  (*@ predicate mem (x: 'a) (s: 'a t) *)
  (** [mem x s] is [x ∈ s]. *)

  (*@ function add (x: 'a) (s: 'a t) : 'a t *)
  (** [add x s] is [s ∪ {x}]. *)

  (*@ function singleton (x: 'a) : 'a t *)
  (** [singleton x] is [{x}]. *)

  (*@ function remove (x: 'a) (s: 'a t) : 'a t *)
  (** [remove x s] is [s ∖ {x}]. *)

  (*@ function union (x: 'a t) (y: 'a t) : 'a t *)
  (** [union x y] is [x ∪ y]. *)

  (*@ function inter (x: 'a t) (y: 'a t) : 'a t *)
  (** [inter x y] is [x ∩ y]. *)

  (*@ predicate disjoint (x: 'a t) (y: 'a t) *)
  (** [disjoint x y] is [x ∩ y = ∅]. *)

  (*@ function diff (x: 'a t) (y: 'a t) : 'a t *)
  (** [diff x y] is [x ∖ y]. *)

  (*@ predicate subset (x: 'a t) (y: 'a t) *)
  (** [subset x y] is [x ⊂ y].*)

  (*@ function cardinal (y: 'a t) : integer *)
  (** [cardinal s] is the number of elements in [s]. *)

  (*@ function choose (s: 'a t) : integer *)
  (** [choose s] is an arbitrary element of [s]. *)

  (*@ function fold (f: 'a -> 'b -> 'b) (s: 'a t) : 'b *)
  (** [fold f s] is [(f xN ... (f x2 (f x1 a))...)], where [x1 ... xN] are the
      elements of s. *)
end

module Set : sig
  (*@ type 'a t *)
  (** The type for finite sets. *)

  (*@ predicate equal (s s': 'a t) *)
  (** [equal s s'] is [s = s']. *)

  (*@ function empty : 'a t *)
  (** [empty] is [∅]. *)

  (*@ predicate is_empty (s: 'a t) *)
  (** [is_empty s] is [s = ∅]. *)

  (*@ predicate mem (x: 'a) (s: 'a t) *)
  (** [mem x s] is [x ∈ s]. *)

  (*@ function add (x: 'a) (s: 'a t) : 'a t *)
  (** [add x s] is [s ∪ {x}]. *)

  (*@ function singleton (x: 'a) : 'a t *)
  (** [singleton x] is [{x}]. *)

  (*@ function remove (x: 'a) (s: 'a t) : 'a t *)
  (** [remove x s] is [s ∖ {x}]. *)

  (*@ function union (x y: 'a t) : 'a t *)
  (** [union x y] is [x ∪ y]. *)

  (*@ function inter (x y: 'a t) : 'a t *)
  (** [inter x y] is [x ∩ y]. *)

  (*@ predicate disjoint (x y: 'a t) *)
  (** [disjoint x y] is [x ∩ y = ∅]. *)

  (*@ function diff (x y: 'a t) : 'a t *)
  (** [diff x y] is [x ∖ y]. *)

  (*@ predicate subset (x y: 'a t) *)
  (** [subset x y] is [x ⊂ y].*)

  (*@ function cardinal (s: 'a t) : integer *)
  (** [cardinal s] is the number of elements in [s]. *)

  (*@ function choose (s: 'a t) : integer *)
  (** [choose s] is an arbitrary element of [s]. *)

  (*@ function fold (f: 'a -> 'b -> 'b) (s: 'a t) : 'b *)
  (** [fold f s] is [(f xN ... (f x2 (f x1 a))...)], where [x1 ... xN] are the
     elements of s. *)
end

module Map : sig
  (* the type ('a, 'b) map is defined internally in GOSPEL and can be
     written as 'a -> 'b *)

  (*@ function ( [<-] ) (m: 'a -> 'b) (x:'a) (y: 'b) : 'a -> 'b *)

  (*@ function ( [_] ) (m: 'a -> 'b) (x: 'a) : 'b *)
end

module Peano : sig
  type t
  (*@ model v: integer *)

  (*@ function int_of_peano (t: t) : integer = t.v *)
  (*@ coercion *)
end
