module FiniteState

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Fin
open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.Seq.Properties
module S = FStar.Seq

let op_Plus_Plus = FStar.List.Tot.Base.append

(* Assume we have an alphabet for strings. *)
(* We won't be running the programs here, merely proving them correct ;*)

assume val sigma: t:Type0{hasEq t}
type string : Type0 = list sigma


(* Define a DFA as a record. 
   We're explicitly representing states as natural numbers. 
   TODO: replace with finite set from library
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

(* The first few lemmas about DFAs follow from the book 
  TODO improve reference *)
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
    assert (d.trans (fin_prod p q) a == fin_prod p' q');
    lem_3_1 x d1 d2 p' q';
    ()


(** Languages and suffixes **)

(* Define a language by its membership function. *)


(* An alternative is:
        type language = string -> bool 
   however, in the logic of F*, this would only represent *decidable* languages,
   since it's a constructive proof. It wouldn't make much different to how we 
   write the proofs. But, it's fundamental, because we've already gone over how
   not all languages can be decideable (since there are more languages than programs,
   i.e. the set of all languages is uncountably infinite. *)

type language = string -> GTot Type0

(* For syntax sugar, we can write this infix as "x `is_in` l" *)
let is_in (s:string) (l:language) = l s

(* Define decidable languages *)
type decider (l:language) = f:(string -> bool){forall x. f x <==> l x}


(* A dfa accepts the language if for every s, s in L <==> d*(s) lands in an accept state *)
val accepts_language : language -> dfa -> GTot Type0
let accepts_language (l:language) (d:dfa) = (forall s. is_in s l <==> d.is_accept (delta_star d d.start s))


(* Define equivalent for a language. Two strings are equivalent if for every suffix, 
   they have the same membership or not *)
let equiv l x y = forall z. ((x ++ z) `is_in` l <==> (y ++ z) `is_in` l)


(** Fooling Pairs and Fooling Sets **)

(* Strings x,y are a fooling pair iff there exists some distinguishing suffiz z, 
     meaning that ((x++z) `is_in` l) is not equal to ((y++z) `is_in l) *)

let xor (p:Type0) (q:Type0) : Type0 = (p /\ ~q) \/ (q /\ ~p)
type foolingsuffix (l:language) x y = (z:string {((x++z) `is_in` l) `xor` ((y++z) `is_in` l)})

type foolingpair l = x:string & y:string & z:foolingsuffix l x y




(* *************************************************
 * Theorem: Infinite fooling sets ==> No DFA accepts
 ***************************************************)

(* Dealing with infinite sets is a little tricky, so the work here is incomplete.

   Here we give a constructive proof of the main lemma that's about DFAs and 
   foolingpairs.        
   This immediately implies that infinite fooling sets => infinite states 

*)

(* A fooling set is a finite set of strings, such that any distinct pair has a 
   fooling suffix. *)
noeq type foolingset (l:language) =  {
  xs:S.seq string;
  map : (i:nat{i<S.length xs}) -> (j:nat{j<S.length xs /\ j=!=i}) -> foolingsuffix l (S.index xs i) (S.index xs j)
}

(* An infinite fooling set means we can construct a fooling set for any size *)
type infinite_foolingset (l:language) = (n:nat) -> (fs:foolingset l{S.length fs.xs > n})

let lem_infinite_foolingset (l:language) (d:dfa) (iff:infinite_foolingset l) : 
  Lemma (requires accepts_language l d) (ensures False) =
    let fs = iff (d.n + 1) in  
    (* g n is defined as the accepting state of the string given
       by the k'th residual class.
       By pigeonhole, g is not injective. *)
    let g (k:fin (d.n + 1)) : state d = 
      delta_star d d.start (S.index fs.xs k) in
    let s : S.seq (state d) = S.init (d.n + 1) g in
    let (i,j) = pigeonhole #d.n s in
    let x = S.index fs.xs i in
    let y = S.index fs.xs j in
    assert (delta_star d d.start x == delta_star d d.start y);

    (* Since fs is a fooling set, there must 
       exist a suffix z such that exactly one of fi++z and fj++z are
       in the original language. *)
    let z = fs.map i j in
    lem_deltastar d d.start d.start x y z




(* Example of using the residual criterion to show that an un-decideable
    language.

     { a^n b^n | n in nat }
   is non-regular.

   How can we encode a language without giving a decider for it? The approach
   will be to give an open definition, by only defining the proposition for 
   a subset of the language. In fact we haven't explicitly stated what the rest
   of the language is.
 *)
assume val symA : sigma
assume val symB : sigma

assume val anbn_lang : language

let rec repeat (c:sigma) (n:nat) : string = if n = 0 then [] else c::repeat c (n-1)

let ambn_string (m:nat) (n:nat) : s:string =
   repeat symA m ++ repeat symB n

(* Here we define decideability for only some strings *)
assume val ambn_decide (m:nat) (n:nat) : m == n <==> ambn_string m n `is_in` anbn_lang

let anbn_lem : infinite_foolingset anbn_lang =
  fun (k:nat) ->
    let xs = S.init (k+1) (repeat symA) in
    let map (m:fin (k+1)) (n:fin (k+1){m =!= n}) : 
        foolingsuffix anbn_lang (S.index xs m) (S.index xs n) = 
          let x = repeat symA m in
          let y = repeat symA n in          
          let z = repeat symB m in
          give_witness (ambn_decide m m);
          give_witness (ambn_decide n m);
          z in
    { xs = xs; map = map }



(* DFA Construction from Fooling sets *)

(* fs is a maximum size fooling set if adding any additional string would 
   make it NOT a fooling set. In other words, for every string s, 
   there exists an x in fs, such that (s,x) is NOT a fooling pair. 
   Our DFA construction relies on a constructive way to map any string to its representative 
   in this set. 
   
   This corresponds to the existence of a Classifier 
    https://hal.archives-ouvertes.fr/hal-01832031/document
   *)
type max_foolingset (l:language) (fs:foolingset l) = (s:string) -> (i:fin (S.length fs.xs){equiv l (S.index fs.xs i) s})

(* Alternate equivalence relation.
   Given a maximum fooling set, two strings are related if their image under this mapping 
   is the same. *)
let equiv_mf (l:language) (fs:foolingset l) (mf:max_foolingset l fs) s1 s2 = (mf s1 = mf s2)

(* The representative of this equivalence class must map to itself *)
val lem_equiv_rep (l:language) (fs:foolingset l) (mf:max_foolingset l fs) (i:nat{i < S.length fs.xs}) :
  Lemma (i == mf (S.index fs.xs i))
let lem_equiv_rep l fs mf i = 
  let j = mf (S.index fs.xs i) in 
    if i = j then () else (
      give_witness (fs.map i j)
    )

(* Equivalence by mf ==> equivalence by suffix *)
val lem_equiv_m2s (l:language) (fs:foolingset l) (mf:max_foolingset l fs) (x:string) (y:string) : Lemma
    (requires equiv_mf l fs mf x y)
    (ensures  equiv l x y)
let lem_equiv_m2s l fs mf x y =
  give_witness (mf x);
  give_witness (mf y);
  let f z : Lemma (l (x ++ z) <==> l (y ++ z)) = () in
  forall_intro f

(* Equivalence by suffix ==> equivalence under mf *)
val lem_equiv_s2m (l:language) (fs:foolingset l) (mf:max_foolingset l fs) (x:string) (y:string) : Lemma
    (requires equiv l x y)
    (ensures equiv_mf l fs mf x y)
let lem_equiv_s2m l fs mf x y = 
  let i = mf x in
  let j = mf y in
    if i = j then () else
      let z = fs.map i j in ()


(* Let x and y be two strings such that [x] = [y]. 
   For every symbol a, we have [x a] = [y a] *)
val lem_mf_equiv (l:language) (fs:foolingset l) (mf:max_foolingset l fs) (x:string) (y:string) (a:sigma) : 
   Lemma 
   (requires equiv_mf l fs mf x y)
   (ensures  equiv_mf l fs mf (x ++ [a]) (y ++ [a]))
let lem_mf_equiv l fs mf x y a = 
  lem_equiv_m2s l fs mf x y;
  let f z : Lemma (l (x ++ [a] ++ z) <==> l (y ++ [a] ++ z)) = (
    append_assoc x [a] z;
    append_assoc y [a] z
  ) in
  forall_intro f;
  lem_equiv_s2m l fs mf (x ++ [a]) (y ++ [a]);
  (* FIXME: What's going wrong here? This assertion passes. And this
  assertion is exactly the current goal. So isn't it here working? *)
  assert (equiv_mf l fs mf (x ++ [a]) (y ++ [a]));
  admit()
  

(* Define the Maximum Fooling Sets to DFA construction *)
val foolingset_to_dfa : (l:language) -> (dec:decider l) -> (fs:foolingset l) -> (mf:max_foolingset l fs) -> dfa
let foolingset_to_dfa l dec fs mf = {
  n = S.length fs.xs;                     (* One state for each string in the fooling set *)
  start = mf [];                          (* Start at the index given by the empty string *)
  trans = (fun q a -> mf (S.index fs.xs q ++ [a])); (*  *)
  is_accept = (fun q -> dec (S.index fs.xs q))      (* States are accepted if the representative
                                                  string is in the language *)
}


(* An "Easy inductive proof" that δ∗([x], z) = [x ++ z] *)
val lem_fs_to_dfa_invariant (l:language) (dec:decider l) (fs:foolingset l) (mf:max_foolingset l fs) (q:fin (S.length fs.xs)): (x:string) -> (z:string) ->
  Lemma 
    (requires q = mf x)
    (ensures (let d = foolingset_to_dfa l dec fs mf in 
       delta_star d q z == mf (x ++ z))) (decreases %[z])
let rec lem_fs_to_dfa_invariant l dec fs mf q x z = 
  let d = foolingset_to_dfa l dec fs mf in match z with 
  | [] -> append_l_nil x
  | a::z' -> (let qa = (d.trans q a) in 
    lem_equiv_rep l fs mf q;
    lem_mf_equiv l fs mf x (S.index fs.xs q) a;
    lem_fs_to_dfa_invariant l dec fs mf qa (x++[a]) z'; 
    append_assoc x [a] z'
  )

(* Completing the correctness proof *)
val lem_fs_to_dfa_correct (l:language) (dec:decider l) (fs:foolingset l) (mf:max_foolingset l fs) :
  Lemma (accepts_language l (foolingset_to_dfa l dec fs mf))
let lem_fs_to_dfa_correct l dec fs mf = 
  let d = foolingset_to_dfa l dec fs mf in 
  let f s : Lemma (l s <==> d.is_accept (delta_star d d.start s)) = (
    lem_fs_to_dfa_invariant l dec fs mf (mf []) [] s;
    let q_final = delta_star d (mf []) s in
    lem_equiv_rep l fs mf q_final;
    lem_equiv_m2s l fs mf (S.index fs.xs q_final) s;
    append_l_nil s;
    append_l_nil (S.index fs.xs q_final)
  ) in forall_intro f
