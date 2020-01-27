module FiniteState

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Squash
open FStar.List.Tot

let op_Plus_Plus = FStar.List.Tot.Base.append

(** The alphabet for strings *)
(* assume val sigma: t:Type0{hasEq t} *)
type sigma = | Z | O
type string : Type0 = list sigma

(** Type for nats within a bound **)
type fin (max:nat) = (n:nat {n < max})

(** **)
noeq type dfa = {
   n : nat;                          (* number of states *)
   start : fin n;                  (* starting state *)
   trans : fin n -> sigma -> fin n;  (* transition function *)
   is_accept : fin n -> bool;       (* accepting states *)
}
type state (d:dfa) = fin d.n

val delta_star : (d:dfa) -> state d -> (s:string) -> Tot (state d) (decreases %[s])
let rec delta_star dfa q s = match s with
  | [] -> q
  | a :: x -> delta_star dfa (dfa.trans q a) x

(** Section 3.3: An identity on DFAs to prove
    ((q, x a) = δ(δ∗(q, x), a)
 **)
val lem1 (x:string) (d:dfa) (q:state d) (a:sigma) : Lemma (delta_star d q (x ++ [a]) == d.trans (delta_star d q x) a)
let rec lem1 x d q a =
  match x with
  | [] -> ()
  | b :: xs ->
    lem1 xs d (d.trans q b) a;
    ()


(* Product Construction *)
val fin_prod (#n1:nat) (#n2:nat) (a:fin n1) (b:fin n2): fin (n1 * n2)
let fin_prod #n1 #n2 a b = 
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


(** Lemma 3.1. δ∗((p, q), w) = δ1∗(p, w), δ2*(q, w)
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
    assert (d.trans (fin_prod p q) a == fin_prod p' q');
    lem_3_1 x d1 d2 p' q';
    ()


(* DFA and Fooling Sets *)

type language = string -> bool
let is_in (s:string) (l:language) = l s


(* Fooling Sets *)
type foolingpair (l:language) = xyz:_{let (x,y,z) = xyz in is_in (x ++ z) l =!= is_in (y ++ z) l}

let accepts_language (l:language) (d:dfa) = (forall s. is_in s l == d.is_accept (delta_star d d.start s))

val lem_deltastar (d:dfa) (q1:state d) (q2:state d) (x:string) (y:string) : (z:string) -> Lemma
  (ensures delta_star d q1  x     == delta_star d q2  y ==>
   delta_star d q1 (x++z) == delta_star d q2 (y ++ z)) (decreases %[x;y])
let rec lem_deltastar d q1 q2 x y z = 
  if (delta_star d q1 x = delta_star d q2 y) then
     match (x,y) with 
     | [], [] -> ()
     | (a :: xs, _) -> 
       lem_deltastar d (d.trans q1 a) q2 xs y z
     | ([], b::ys) -> lem_deltastar d q1 (d.trans q2 b) x ys z
  else ()

val lem_foolingsets (l:language) (xyz:foolingpair l) : (d:dfa) -> Lemma 
  (requires (accepts_language l d))
  (ensures (let (x,y,z) = xyz in 
           delta_star d d.start x =!= delta_star d d.start y))
let lem_foolingsets l xyz d = let (x,y,z) = xyz in
  lem_deltastar d d.start d.start x y z

(* Towards pigeon hole principle and counting fooling sets *)
type foolingset (l:language) = xs:(list string) {forall (i:nat{i<length xs}) (j:nat{j<length xs}). exists (z:string).
                  l (index xs i ++ z) =!= l (index xs j ++ z)}

type infinite_foolingset (l:language) = (n:nat) -> (fs:foolingset l{length fs > n})
(* TODO *)
(* I can state the lemma that infinite fooling sets => no DFA accepts it, but
   not sure how to prove this *)
val lem_infinite_foolingset (l:language) (d:dfa) (fs:infinite_foolingset l) : (n:nat) -> Lemma (requires accepts_language l d) (ensures d.n >= n)


(* NFAs *)
(* TODO *)
