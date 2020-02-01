module DFA

(* This is a presentation in F* of some theory about decidable
   languages and Deterministic Finite-state Automata (DFAs).

   The main goal is to state and prove the following two theorem 
   statements:

     (1) A language cannot be recognized by a DFA if it 
     has an infinite number of residual classes.

     (2) If a decidable language has a finite number of 
     residual classes, then it can be recognized by a DFA.

   This is a retelling of the Myhill-Nerode theorem, which is
   usually presented in terms of sets of equivalence relations.
   In F*, it is slightly more subtle because we have to be explicit
   explicit about how we use constructive forms.
   It requires care, for example, to state that a language is regular
   without presuming that the language is decidable.

   The code here directly follows the approach described in Doczkal 
   and Smolka. [1] A starting point was the F* regular expressions
   from Chajed [2]. Some of the comments are intended to draw connections 
   to course notes on DFAs and the Myhill-Nerode theorem [3].

   [1] Regular Language Representations in the Constructive
   Type Theory of Coq
   Christian Doczkal, Gert Smolka
   https://hal.archives-ouvertes.fr/hal-01832031/document

   [2] Regular Expression Derivatives in F*. Tej Chajed. 
     https://github.com/tchajed/regex-derivative

   [3] Models of Computation. Jeff Erickson.
   http://jeffe.cs.illinois.edu/teaching/algorithms/models/all-models.pdf
*)
open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Fin
open FStar.Classical
open FStar.Tactics.Logic
open FStar.Squash
module S = FStar.Seq

let op_Plus_Plus = FStar.List.Tot.Base.append

(* The alphabet is a finite set with decidable equality *)
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



(** Languages **)

(* A language is defined by giving a proposition for every string.
   Importantly, this encoding does not presume that languages are 
   decidable.
    *)

type language = string -> GTot Type0

(* For syntax sugar, we can write this infix as "x `is_in` l" *)
let is_in (s:string) (l:language) = l s

(* Define extensional equivalence for a language. *)
let equiv (l1:language) (l2:language) = forall s. (s `is_in` l1 <==> s `is_in` l2)


(* A decider is a constructive proof that the language is decidable. *)
type decider (l:language) = f:(string -> bool){forall x. f x <==> l x}
   

(* A dfa accepts the language if for every s, s in L <==> d*(s) lands in an accept state *)
val accepts : dfa -> language -> GTot Type0
let accepts (d:dfa) (l:language) = (forall s. is_in s l <==> d.is_accept (delta_star d d.start s))



(** Residuals and Classifiers **)

(* Residual language, also written as a quotient language {x}/L *)
val residual (l:language) (x:string) : language
let residual l x y = (x ++ y) `is_in` l


(* Residual Criterion *)
(* The residuals of a language form an equivalence class.

   This is an instance of a Myhill-Nerode relation. The representatives
   of each class correspond to a "fooling set" [3]  , and the partitinocorresponds
   closely to the fooling set.

   The residual criterion is that an infinite number of such 
   This is encoded as a function f that for each nat selects a distinct
   residual language. 

   *)
let residual_criterion (l:language) (f:nat -> string) = 
  forall m n. n == m <==> residual l (f m) `equiv` residual l (f n)

(* Theorem 4.6 Residual Criterion *)
let xor p q = (p /\ ~q) \/ (q /\ ~p)

let thm_4_6 (l:language) (d:dfa) (f:nat -> string{residual_criterion l f}) : 
  Lemma (requires accepts d l) (ensures False) = 
    (* g n is defined as the accepting state of the string given
       by the n'th residual class.
       By pigeon hole, g must not be injective. *)
    let g (n:nat) : state d = delta_star d d.start (f n) in
    let s : S.seq (state d) = S.init (d.n + 1) g in
    let (i,j) = pigeonhole #d.n s in
    let fi = f i in
    let fj = f j in

    (* Since the residuals of fi,fj are non-equivalent, there must 
       exist a suffix y such that exactly one of fi++x and fi++y are
       in the original language. *)
    assert(~(residual l fi `equiv` residual l fj));
    let pf = get_proof (exists y. l (fi ++ y) `xor` l (fj ++ y)) in

    (* But since d*(fi) == d*(fj), the dfa accepts the same for any
       suffix. This is the contradiction. *)
    let f (y:string{l (fi ++ y) `xor` l (fj ++ y)}) : GTot (squash False) =
           lem_deltastar d d.start d.start fi fj y
      in exists_elim (False) pf f


(* Example 4.7 *)
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

let anbn_lem () : Lemma (residual_criterion anbn_lang (repeat symA)) =
    let rec f (m:nat) (n:nat) : Lemma (n == m <==> 
                          residual anbn_lang (repeat symA m) `equiv` 
                          residual anbn_lang (repeat symA n)) =
        if (n = m) then () else 
        if (n < m) then f n m else (
          assert(m < n);
          (* Have to show that any two residual languages in this 
             enumeration are non-equivalent. 
             z=b^m is an accepting suffix of a^m,
             but is not an accepting suffix of a^n   *)
          let x = repeat symA m in
          let y = repeat symA n in          
          let z = repeat symB m in
          give_witness (ambn_decide m m);
          give_witness (ambn_decide n m)
        )
    in forall_intro_2 f



(* Definition 5.1 *)
type classifier (n:nat) = f:(string -> fin n){forall x y a. f x = f y ==> f (x ++ a) = f (y ++ a)}



(* Lemma 5.2 *)
(* We need to define some auxiliary list operations here. 
   Couldn't find these in the std library. *)
let rec take (n:nat) (x:string{n < length x}) : s:string{length s = n} = 
  if n = 0 then [] else
  let a::y = x in a :: take (n-1) y

let rec drop (n:nat) (x:string{n < length x}) : s:string{length s = length x - n} =
  if n = 0 then x else
  let a::y = x in drop (n-1) y

let rec lem_take_drop (n:nat) (x:string{n < length x}) : 
  Lemma (take n x ++ drop n x == x) =
    if n = 0 then ()
    else let a::y = x in lem_take_drop (n-1) y


let lem_5_2 (#n:nat{n>=1}) (f:classifier n) (x:string{n < length x}): 
  (y:string{length y < length x /\ f x == f y}) =
  (* By pigeonhole, there must exist i < j < length x, 
     f (x[:i]) = f (x[:j]). *)
  let s : S.seq (fin n) = S.init (n+1) (fun i -> f (take i x)) in
  let (i,j) = pigeonhole #n s in
  (* We can then take x[:i] ++ x[j:] as a smaller string same image under f *)
  lem_take_drop j x;
  append_length (take i x) (drop j x);
  take i x ++ drop j x


(* Theorem 5.3 (Cut-Off) *)
val thm_cutoff_left (#n:nat) (f:classifier n) (p:fin n -> Type0) (x:string{p (f x)}) : Tot (y:string{length y <= n /\ p (f y)}) (decreases %[length x])
let rec thm_cutoff_left #n f p x = 
  if length x <= n then x else thm_cutoff_left f p (lem_5_2 f x)

let thm_cutoff_right (#n:nat) (f:classifier n) (p:fin n -> Type0) (x:string{length x < n /\ p (f x)}) :
  Lemma (ensures exists x. p (f x)) =
  ()

let thm_cutoff (#n:nat) (f:classifier n) (p:fin n -> Type0) : 
  Lemma ((exists x. p x) <==> (exists x. length x < n /\ p (f x))) =
  (* TODO: clearly follows from thm_cutoff_left and thm_cutoff_right,
     but I need to figure out how to elim the <==> and exists *)
  admit() 


(* Corollary 5.4 Let f : Σ∗ → Q be a classifier. 
 Then ∃x. p(f x) and ∀x. p(f x) are decidable
 for all decidable predicates p : Q → B.*)

let coro_5_4 (#n:nat) (p:fin n -> bool) (f:classifier n) : b:bool{b <==> (exists x. p x)} =
    let pp (q:fin n) : Type0 = p q in
    (* TODO: The only way to compute b is to enumerate all of the fin types. 
       So far, the way we're encoding sigma does NOT allow us to enumerate 
       it. *)
    (* By 5_4, if any string exists, then one with length fin_n exists.
       Since is finite, we can enumerate each one. *)

    admit()
  

(* Corollary 5.5 Let f : Σ∗ → Q be a classifier.
 Then the image of f can be constructed as a subtype of Q.
 TODO: what does it mean in f* to construct the subtype?
*)
type of_class (#n:nat) (l:language) (f:classifier n) = q:fin n {exists x. f x = q}



(* Definition 5.6 Refines *)
(* DFA acceptance defines a language. *)
let refines (#n:nat) (f:classifier n) (l:language) = 
  forall x y. (f x == f y) ==> (x `is_in` l <==> y `is_in` l)

let lang_dfa (d:dfa) : language = 
  fun x -> d.is_accept (delta_star d d.start x)

let lang_dfa_dec (d:dfa) : decider (lang_dfa d) =
  fun x -> d.is_accept (delta_star d d.start x)

(* Fact 5.7 *)
(* The DFA "walk" is a classifier that refines the language it accepts.*)
let delta_hat (d:dfa) : (f:classifier d.n{f `refines` (lang_dfa d)}) =
  let f x = delta_star d d.start x in
  let g x y a : Lemma (f x == f y ==> f (x ++ a) == f (y ++ a)) = 
     lem_deltastar d d.start d.start x y a in
  forall_intro_3 g; f


(* Lemma 5.8 *)
(* Construct a DFA from the classifier (and decider) *)
let lem_5_8 (l:language) (#n:nat) (dec:decider l) (f:classifier n{f `refines` l}): 
  (d:dfa {d `accepts` l}) =
  let d = {
    n = n;
    start = f [];
    trans = (fun q a -> admit());
    is_accept = coro_5_4 (d (f 
  } in admit()
