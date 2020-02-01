module DFAs

(* An encoding in F* of Deterministic Finite-state Automata (DFAs).
   See MyhillNerode.fst for more. *)
open FStar.Mul
open FStar.Math.Lemmas
open FStar.Fin
open FStar.List.Tot

let op_Plus_Plus = FStar.List.Tot.Base.append


(* Assume we have an alphabet for strings. *)
assume val sigma: t:Type0{hasEq t}
type string : Type0 = list sigma


(* Define a DFA as a record. 
   We're explicitly representing states as natural numbers. 
 *)
noeq type dfa = {
   n : nat;                          (* number of states *)
   start : fin n;                  (* starting state *)
   trans : fin n -> sigma -> fin n;  (* transition function *)
   is_accept : fin n -> bool;       (* accepting states *)
}
type state (d:dfa) = fin d.n

(* Here's the inductive definition for a string-directed walk through the DFA *)
val delta_star : (d:dfa) -> state d -> (s:string) -> Tot (state d) (decreases %[s])
let rec delta_star dfa q s = match s with
  | [] -> q
  | a :: x -> delta_star dfa (dfa.trans q a) x

(* The first few lemmas about DFAs follow directly from the course notes.[3]*)
(* Section 3.3: An identity on DFAs to prove
    δ∗(q, x a) = δ(δ∗(q, x), a)
 *)
val lem_3_3 (x:string) (d:dfa) (q:state d) (a:sigma) : 
  Lemma (delta_star d q (x ++ [a]) == d.trans (delta_star d q x) a)
let rec lem_3_3 x d q a =
  match x with
  | [] -> ()
  | b :: xs -> lem_3_3 xs d (d.trans q b) a


(* Inductive lemma about d*. For if d*(x) and d*(y) land in the same state, then for any 
   suffix z, d*(x++z) and d*(y++z) land in the same state. 
    This seems to require two induction steps, TODO simplify? *)
val lem_deltastar (d:dfa) (q1:state d) (q2:state d) (x:string) (y:string) : (z:string) -> Lemma
  (ensures delta_star d q1  x     == delta_star d q2  y ==>
           delta_star d q1 (x++z) == delta_star d q2 (y ++ z)) (decreases %[x;y])
let rec lem_deltastar d q1 q2 x y z = 
  if (delta_star d q1 x = delta_star d q2 y) then
     match (x,y) with 
     | [], [] -> ()
     | (a :: xs, _) -> lem_deltastar d (d.trans q1 a) q2 xs y z
     | (_, b :: ys) -> lem_deltastar d q1 (d.trans q2 b) x ys z
  else ()


(* Product Construction *)
(* Since we've chosen explicit numbers to represent states, we have to describe how 
   to map back and forth between pairs of states (x,y) and (x*|Y| + y). *)

val fin_prod (#n1:nat) (#n2:nat) (a:fin n1) (b:fin n2): fin (n1 * n2)
let fin_prod #n1 #n2 a b = 
  (* This lemma was necessary to look up from the math library, to
     prove that a*n2 + b < n1 * n2 as required *)
  lemma_eucl_div_bound b a n2;
  (a * n2) + b

val product_dfa : (d1:dfa) -> (d2:dfa) -> dfa
let product_dfa d1 d2 = {
        n = d1.n * d2.n;
        start = fin_prod d1.start d2.start;
        trans = (fun s a -> let s1 = s / d2.n in
                         let s2 = s % d2.n in
                         fin_prod (d1.trans s1 a) (d2.trans s2 a));
        is_accept = (fun s -> let s1 = s / d2.n in
                           let s2 = s % d2.n in
                           d1.is_accept s1 && d2.is_accept s2);
  }


(** Lemma 3.1. An inductive proof about the product construction
  δ∗((p, q), w) = δ1∗(p, w), δ2*(q, w)
**)

val lem_3_1 (w:string) (d1:dfa) (d2:dfa) (p:state d1) (q:state d2) : Lemma (
  let d = product_dfa d1 d2 in
  delta_star d (fin_prod p q) w ==
  fin_prod (delta_star d1 p w) (delta_star d2 q w))
let rec lem_3_1 w d1 d2 p q = 
  let d = product_dfa d1 d2 in
  match w with
  | [] -> ()
  | a :: x -> 
    let p' = d1.trans p a in
    let q' = d2.trans q a in
    lemma_div_mod_plus q p d2.n;
    assert (d.trans (fin_prod p q) a = fin_prod p' q');
    lem_3_1 x d1 d2 p' q';
    ()
