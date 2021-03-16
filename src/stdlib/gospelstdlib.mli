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

   predicate (=) (s s': 'a)
*)

(** Arithmetic

   The type [integer] is built-in. This is the type of arbitrary precision integers,
   not to be confused with OCaml's type [int] (machine integers).

   There is a coercion from type [int] to type [integer], so that GOSPEL specifications
   can be written using type [integer] only, and yet use OCaml's variables of type [int].
*)

(*@ function (+)   (s s': integer) : integer *)
(*@ function (-)   (s s': integer) : integer *)
(*@ function ( * ) (s s': integer) : integer *)
(*@ function (/)   (s s': integer) : integer *)
(*@ function mod   (s s': integer) : integer *)
(*@ function (-_)  (x: integer) : integer *)
(*@ predicate (>)  (s s': integer) *)
(*@ predicate (>=) (s s': integer) *)
(*@ predicate (<)  (s s': integer) *)
(*@ predicate (<=) (s s': integer) *)

type int

(*@ function integer_of_int (x: int) : integer *)
(*@ coercion *)

(*@ function abs (x:integer) : integer = if x >= 0 then x else -x *)

(*@ function min (s s' : integer) : integer
    = if x <= y then x else y *)

(*@ function max (s s' : integer) : integer
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

  (*@ predicate equal (s s': 'a t) *)
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

  (*@ function append (s s': 'a t) : 'a t *)
  (** [append s s'] is the sequence [x] followed by the sequence [y]. *)

  (*@ function (++) (s s': 'a t) : 'a t *)
  (** [x ++ y] is [append s s']. *)

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

<<<<<<< Updated upstream
type 'a array
(*@ ephemeral *)
(*@ mutable model contents: 'a seq *)
(*@ model array_length: integer *)
(*@ invariant array_length = length contents *)

(*@ function elts (a: 'a array): 'a seq = a.contents *)
(*@ coercion *)
||||||| constructed merge base
type 'a array
(*@ ephemeral
    mutable model contents: 'a seq
    model array_length: integer
    invariant array_length = length contents *)

(*@ function elts (a: 'a array): 'a seq = a.contents *)
(*@ coercion *)
=======
(*@ type 'a array *)
>>>>>>> Stashed changes

module Array : sig
  (*@ type 'a t = 'a array *)
  (** An alias for the type of arrays. *)

  (*@ function length (a: 'a t) : integer *)
  (** Return the length (number of elements) of the given array. *)

  (*@ function get (a: 'a t) (i: integer) : 'a *)
  (** [get a i] is the element number [i] of array [a]. *)

  (*@ function ([_]) (a: 'a t) (i: integer) : 'a *)
  (** [a.\[i\]] is get a i. *)

  (*@ function make (n: integer) (x: 'a) : 'a t *)
  (** [make n x] is an array of length [n], initialized with [x]. *)

  (*@ function init (n: integer) (f: integer -> 'a) : 'a t *)
  (** [init n f] is an array of length [n], with element number [i] initialized
      to the result of [f i]. *)

  (*@ function append (a b: 'a t) : 'a t *)
  (** [append v1 v2] returns an array containing the concatenation of [v1] and
      [v2]. *)

  (*@ function concat (a: 'a t list) : 'a t *)
  (** Same as {!append}, but concatenates a list of arrays. *)

  (*@ function sub (a: 'a array) -> (i len: integer) : 'a array *)
  (** [sub a pos len] is the array of length [len], containing the elements
      number [pos] to [pos + len - 1] of array [a]. *)

  (*@ function map (f: 'a -> 'b) (a: 'a t) : 'b t *)
  (** [map f a] applies function [f] to all the elements of [a], and builds an
      array with the results returned by [f] *)

  (*@ function mapi (f: integer -> 'a -> 'b) (a: 'a t) : 'b t *)
  (** Same as {!map}, but the function is applied to the index of the element as
      first argument, and the element itself as second argument. *)

  (*@ function fold_left (f: 'a -> 'b -> 'a) (init: 'a) (a: 'b t) : 'a *)
  (** [fold_left f init a] is [f (... (f (f init a[0]) a[1]) ...) a[n-1]], where
      [n] is the length of [a]. *)

  (*@ function fold_right (f: 'b -> 'a -> 'a) (a: 'b t) (init: 'a) : 'a *)
  (** [fold_right f a init] is [f a[0] (f a[1] ( ... (f a[n-1] init) ...))],
      where [n] is the length of [a]. *)

  (*@ function map2 (f: 'a -> 'b -> 'c) (a: 'a t) (b: 'b t) : 'c t *)
  (** [map2 f a b] applies function [f] to all the elements of [a] and [b], and
      builds an array with the results returned by [f]. *)

  (*@ predicate for_all (f: 'a -> bool) (a: 'a array) *)
  (** [for_all f a] checks if all elements of [a] satisfy the predicate [f]. *)

  (*@ predicate exists (f: 'a -> bool) (a: 'a array) *)
  (** [exists f a] checks if at least one element of [a] satisfies [f]. *)

  (*@ predicate for_all2 (f: 'a -> 'b -> bool) (a: 'a array) (b: 'b array) *)
  (** Same as {!for_all}, but for a two-argument predicate. *)

  (*@ predicate exists2 (f: 'a -> 'b -> bool) (a: 'a array) (b: 'b array) *)
  (** Same as {!exists}, but for a two-argument predicate. *)

  (*@ predicate mem (x: 'a) (a: 'a array) *)
  (** [mem x a] holds iff [x] is equal to an element of [a] *)

  (*@ function to_list (b: 'a t) : 'a list *)
  (*@ function of_list (b: 'a list) : 'a t *)

  (*@ function to_seq (b: 'a t) : 'a Seq.t *)
  (*@ function of_seq (b: 'a Seq.t) : 'a t *)
end

(** Finite unordered multisets. *)
module Bag : sig
  (*@ type 'a t *)
  (** The type for finite bags. *)

  (*@ function occurences (x: 'a) (b: 'a t): integer *)
  (** [occurences x b] is the number of occurences of [x] in [s]. *)

  (*@ function compare (b b': 'a t) : int *)
  (** A comparison function over bags. *)

  (*@ predicate equal (b b': 'a t) *)
  (** [equal b b'] is [b = b']. *)

  (*@ function empty : 'a t *)
  (** [empty] is [∅]. *)

  (*@ predicate is_empty (b: 'a t) *)
  (** [is_empty b] is [b = ∅]. *)

  (*@ predicate mem (x: 'a) (b: 'a t) *)
  (** [mem x b] is [x ∈ b]. *)

  (*@ function add (x: 'a) (b: 'a t) : 'a t *)
  (** [add x b] is [b ∪ {x}]. *)

  (*@ function singleton (x: 'a) : 'a t *)
  (** [singleton x] is [{x}]. *)

  (*@ function remove (x: 'a) (b: 'a t) : 'a t *)
  (** [remove x b] is [b ∖ {x}]. *)

  (*@ function union (b b': 'a t) : 'a t *)
  (** [union b b'] is [b ∪ b']. *)

  (*@ function sum (b b': 'a t) : 'a t *)
  (** [union b b'] is [b ∪ b']. *)

  (*@ function inter (b b': 'a t) : 'a t *)
  (** [inter b b'] is [b ∩ b']. *)

  (*@ predicate disjoint (b b': 'a t) *)
  (** [disjoint b b'] is [b ∩ b' = ∅]. *)

  (*@ function diff (b b': 'a t) : 'a t *)
  (** [diff b b'] is [b ∖ b']. *)

  (*@ predicate subset (b b': 'a t) *)
  (** [subset b b'] is [b ⊂ b']. *)

  (*@ function cardinal (b: 'a t) : integer *)
  (** [cardinal b] is the number of elements in [b]. *)

  (*@ function choose (b: 'a t) : integer *)
  (** [choose b] is an arbitrary element of [b]. *)

  (*@ function map (f: 'a -> 'b) (b: 'a t) : 'b t *)
  (** [map f b] is a fresh set which elements are [f x1 ... f xN], where [x1 ...
      xN] are the elements of [b]. *)

  (*@ function fold (f: 'a -> 'b -> 'b) (b: 'a t) : 'b *)
  (** [fold f b] is [(f xN ... (f x2 (f x1 a))...)], where [x1 ... xN] are the
      elements of [b]. *)

  (*@ predicate for_all (f: 'a -> bool) (b: 'a t) *)
  (** [for_all f b] holds iff [f x] is [true] for all elements in [b]. *)

  (*@ predicate exists (f: 'a -> bool) (b: 'a t) *)
  (** [for_all f b] holds iff [f x] is [true] for at least one element in [b]. *)

  (*@ function filter (f: 'a -> bool) (b: 'a t) : 'a t *)
  (** [filter f b] is the bag of all elements in [b] that satisfy [f]. *)

  (*@ function filter_map (f: 'a -> 'a option) (b: 'a t) : 'a t *)
  (** [filter_map f b] is the bag of all [v] such that [f x = Some v] for some
      element [x] of [b]. *)

  (*@ function partition (f: 'a -> bool) (b: 'a t) : ('a t * 'a t) *)
  (** [partition f b] is the pair of bags [(b1, b2)], where [b1] is the bag of
      all the elements of [b] that satisfy [f], and [b2] is the bag of all the
      elements of [b] that do not satisfy [f]. *)

  (*@ function cardinal (b: 'a t) : int *)
  (** [cardinal b] is the number of distinct elements in [b]. *)

  (*@ function elements (b: 'a t) : 'a list *)
  (** [elements b] is the list of all elements in [b]. *)

  (*@ function choose (b: 'a t) : 'a *)
  (*@ requires not (is_empty b) *)
  (** [choose b] is an arbitrary element of [b]. *)

  (*@ choose_opt (b: 'a t) : 'a option *)
  (** [choose b] is an arbitrary element of [b] or [None] if [b] is empty. *)

  (*@ function to_list (b: 'a t) : 'a list *)
  (*@ function of_list (b: 'a list) : 'a t *)

  (*@ function to_seq (b: 'a t) : 'a Seq.t *)
  (*@ function of_seq (b: 'a Seq.t) : 'a t *)
end

(** Finite unordered sets. *)
module Set : sig
  (*@ type 'a t *)
  (** The type for finite sets. *)

  (*@ function compare (s s': 'a t) : int *)
  (** A comparison function over sets. *)

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

  (*@ function union (s s': 'a t) : 'a t *)
  (** [union s s'] is [s ∪ s']. *)

  (*@ function inter (s s': 'a t) : 'a t *)
  (** [inter s s'] is [s ∩ s']. *)

  (*@ predicate disjoint (s s': 'a t) *)
  (** [disjoint s s'] is [s ∩ s' = ∅]. *)

  (*@ function diff (s s': 'a t) : 'a t *)
  (** [diff s s'] is [s ∖ s']. *)

  (*@ predicate subset (s s': 'a t) *)
  (** [subset s s'] is [s ⊂ s']. *)

  (*@ function cardinal (s: 'a t) : integer *)
  (** [cardinal s] is the number of elements in [s]. *)

  (*@ function choose (s: 'a t) : integer *)
  (** [choose s] is an arbitrary element of [s]. *)

  (*@ function map (f: 'a -> 'b) (s: 'a t) : 'b t *)
  (** [map f s] is a fresh set which elements are [f x1 ... f xN], where [x1 ...
      xN] are the elements of [s]. *)

  (*@ function fold (f: 'a -> 'b -> 'b) (s: 'a t) : 'b *)
  (** [fold f s] is [(f xN ... (f x2 (f x1 a))...)], where [x1 ... xN] are the
      elements of [s]. *)

  (*@ predicate for_all (f: 'a -> bool) (s: 'a t) *)
  (** [for_all f s] holds iff [f x] is [true] for all elements in [s]. *)

  (*@ predicate exists (f: 'a -> bool) (s: 'a t) *)
  (** [for_all f s] holds iff [f x] is [true] for at least one element in [s]. *)

  (*@ function filter (f: 'a -> bool) (s: 'a t) : 'a t *)
  (** [filter f s] is the set of all elements in [s] that satisfy [f]. *)

  (*@ function filter_map (f: 'a -> 'a option) (s: 'a t) : 'a t *)
  (** [filter_map f s] is the set of all [v] such that [f x = Some v] for some
      element [x] of [s]. *)

  (*@ function partition (f: 'a -> bool) (s: 'a t) : ('a t * 'a t) *)
  (** [partition f s] is the pair of sets [(s1, s2)], where [s1] is the set of
      all the elements of [s] that satisfy the predicate [f], and [s2] is the set
      of all the elements of [s] that do not satisfy [f]. *)

  (*@ function cardinal (s: 'a t) : int *)
  (** [cardinal s] is the number of elements in [s]. *)

  (*@ function elements (s: 'a t) : 'a list *)
  (** [elements s] is the list of all elements in [s]. *)

  (*@ function choose (s: 'a t) : 'a *)
  (*@ requires not (is_empty s) *)
  (** [choose s] is an arbitrary element of [s]. *)

  (*@ choose_opt: t -> elt option *)
  (** [choose s] is an arbitrary element of [s] or [None] if [s] is empty. *)

  (*@ function to_list (b: 'a t) : 'a list *)
  (*@ function of_list (b: 'a list) : 'a t *)

  (*@ function to_seq (b: 'a t) : 'a Seq.t *)
  (*@ function of_seq (b: 'a Seq.t) : 'a t *)
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
