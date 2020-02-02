module MyhillNerode

(* This is a presentation in F* of some theory about decidable
   languages and Deterministic Finite-state Automata (DFAs).

   The main goal is to state and prove the following two theorem 
   statements:

     (1) A language cannot be recognized by a DFA if it 
     has an infinite number of residual classes (fooling sets).

     (2) If a decidable language has a finite number of residual
     classes, then it can be recognized by a DFA.

   This is a retelling of the Myhill-Nerode theorem, which is
   usually presented in terms of sets of equivalence relations.
   In F*, it is slightly more subtle because we have to be explicit
   explicit about how we use constructive forms.
   It requires care, for example, to state that a language is regular
   without presuming that the language is decidable.

   The code here mainly follows the "fooling sets" notion from
   course nodes on DFAs and the Myhill-Nerode theorem [3], as well
   as the notion of residual classes and classifiers from Doczkal 
   and Smolka [1]. Inspiration for the F* encoding comes from Chajed [2].

   [1] Regular Language Representations in the Constructive
   Type Theory of Coq
   Christian Doczkal, Gert Smolka
   https://hal.archives-ouvertes.fr/hal-01832031/document

   [2] Regular Expression Derivatives in F*. Tej Chajed. 
     https://github.com/tchajed/regex-derivative

   [3] Models of Computation. Jeff Erickson.
   http://jeffe.cs.illinois.edu/teaching/algorithms/models/all-models.pdf
*)

open DFAs
open FStar.Classical
open FStar.Fin
open FStar.List.Tot
module S = FStar.Seq

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



(** Residual Classes and Fooling Sets **)

(* Residual language, also written as a quotient language {x}/L *)
val residual (l:language) (x:string) : language
let residual l x y = (x ++ y) `is_in` l

(* Two strings are equivalent under a language if their residual languages
   are equivalent. *)
let equiv_r l x y = residual l x `equiv` residual l y

(* We call two strings x,y a fooling pair if we have a witness z that 
   they belong to different residual classes. *)
let xor (p:Type0) (q:Type0) : Type0 = (p /\ ~q) \/ (q /\ ~p)
type foolingsuffix (l:language) x y = (z:string {((x++z) `is_in` l) `xor` ((y++z) `is_in` l)})
type foolingpair l = x:string & y:string & z:foolingsuffix l x y

(* A fooling set is a sequence of strings that represent different residual
   classes. *)
noeq type foolingset (l:language) =  {
  xs:S.seq string;
  map : (i:nat{i<S.length xs}) -> (j:nat{j<S.length xs /\ j=!=i}) -> 
                foolingsuffix l (S.index xs i) (S.index xs j)
}


(* *************************************************
 * Theorem: Infinite fooling sets ==> No DFA accepts
 ***************************************************)

(* A constructive proof that there is no maximum size fooling set is
 encoded as a function that gives a fooling of any finite size. 
   This corresponds to the residual criteron [1]. *)
type infinite_foolingset (l:language) = (n:nat) -> (fs:foolingset l{S.length fs.xs > n})


(* Theorem 4.6 Residual Criterion *)
let lem_infinite_foolingset (#l:language) (d:dfa) (iff:infinite_foolingset l) : 
  Lemma (requires d `accepts` l) (ensures False) =
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




(* Example of using the residual criterion to show that the language
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

(* If we have a fooling set fs of maximum size, then adding any new 
   string must belong to one of the same residual classes.
   A constructive proof of this is a classifier [1], that maps any
   string to a member of fs that is in the same residual class.
   *)
type classifier (#l:language) (fs:foolingset l)
  = (s:string) -> (i:fin (S.length fs.xs){equiv_r l (S.index fs.xs i) s})


(* A classifier defines an alternate equivalence relation on strings:
   Two strings are related if their image under this mapping 
   is the same. Before proceeding with the DFA construction, we 
   show that these equivalence relations are isomorphic. *)
let equiv_cls (#l:language) (#fs:foolingset l) (c:classifier fs) s1 s2 = (c s1 == c s2)

(* The representative of this equivalence class must map to itself *)
val lem_equiv_rep (#l:language) (#fs:foolingset l) (c:classifier fs) (i:nat{i < S.length fs.xs}) :
  Lemma (i == c (S.index fs.xs i))
let lem_equiv_rep #l #fs mf i = 
  let j = mf (S.index fs.xs i) in 
    if i = j then () else (
      give_witness (fs.map i j)
    )

(* Equivalence by mf ==> equivalence by suffix *)
val lem_equiv_m2s (#l:language) (#fs:foolingset l) (c:classifier fs) (x:string) (y:string) : Lemma
    (requires equiv_cls c x y)
    (ensures  equiv_r l x y)
let lem_equiv_m2s #l #fs c x y =
  give_witness (c x);
  give_witness (c y);
  let f z : Lemma (l (x ++ z) <==> l (y ++ z)) = () in
  forall_intro f

(* Equivalence by suffix ==> equivalence under mf *)
val lem_equiv_s2m (#l:language) (#fs:foolingset l) (c:classifier fs) (x:string) (y:string) : Lemma
    (requires equiv_r l x y)
    (ensures equiv_cls c x y)
let lem_equiv_s2m #l #fs c x y = 
  let i = c x in
  let j = c y in
    if i = j then () else
      let z = fs.map i j in ()

(* Let x and y be two strings such that [x] = [y]. 
   For every symbol a, we have [x a] = [y a] *)
val lem_mf_equiv (#l:language) (#fs:foolingset l) (c:classifier fs) (x:string) (y:string) (a:sigma) : 
   Lemma 
   (requires equiv_cls c x y)
   (ensures  equiv_cls c (x ++ [a]) (y ++ [a]))
let lem_mf_equiv #l #fs c x y a = 
  lem_equiv_m2s c x y;
  let f z : Lemma (l (x ++ [a] ++ z) <==> l (y ++ [a] ++ z)) = (
    append_assoc x [a] z;
    append_assoc y [a] z
  ) in
  forall_intro f;
  lem_equiv_s2m c (x ++ [a]) (y ++ [a])


(* Now we can define the Maximum Fooling Sets to DFA construction *)
val classifier_to_dfa : (#l:language) -> (dec:decider l) -> (#fs:foolingset l) -> (c:classifier fs) -> dfa
let classifier_to_dfa #l dec #fs c = {
  n = S.length fs.xs;                   (* One state for each string in the fooling set *)
  start = c [];                         (* Start at the index given by the empty string *)
  trans = (fun q a -> c (S.index fs.xs q ++ [a]));
  is_accept = (fun q -> dec (S.index fs.xs q))    
            (* States are accepting iff the representative
            string is in the language *)
}

(* An "Easy inductive proof" that δ∗([x], z) = [x ++ z] *)
val lem_fs_to_dfa_invariant (#l:language) (dec:decider l) (#fs:foolingset l) (c:classifier fs) (q:fin (S.length fs.xs)): (x:string) -> (z:string) ->
  Lemma 
    (requires q = c x)
    (ensures (let d = classifier_to_dfa dec c in 
       delta_star d q z == c (x ++ z))) (decreases %[z])
let rec lem_fs_to_dfa_invariant #l dec #fs c q x z = 
  let d = classifier_to_dfa dec c in match z with 
  | [] -> append_l_nil x
  | a::z' -> (let qa = (d.trans q a) in 
    lem_equiv_rep c q;
    lem_mf_equiv c x (S.index fs.xs q) a;
    lem_fs_to_dfa_invariant dec c qa (x++[a]) z';
    append_assoc x [a] z'
  )

(* Completing the correctness proof *)
val lem_fs_to_dfa_correct (#l:language) (dec:decider l) (#fs:foolingset l) (c:classifier fs) :
  Lemma ((classifier_to_dfa dec c) `accepts` l)
let lem_fs_to_dfa_correct #l dec #fs c = 
  let d = classifier_to_dfa dec c in 
  let f s : Lemma (l s <==> d.is_accept (delta_star d d.start s)) = (
    lem_fs_to_dfa_invariant dec c (c []) [] s;
    let q_final = delta_star d (c []) s in
    lem_equiv_rep c q_final;
    lem_equiv_m2s c (S.index fs.xs q_final) s;
    append_l_nil s;
    append_l_nil (S.index fs.xs q_final)
  ) in forall_intro f
