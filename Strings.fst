module Strings


(* Define the alphabet *)
type symbol =
    | SymA : symbol
    | SymB : symbol
    | SymC : symbol

(* Inductive definition of string *)
type string = 
    | Empty : string
    | Cons : symbol -> string -> string

(* Function definition of concatenation *)
val concat : string -> string -> string
let rec concat w v = match w with
    | Empty -> v
    | Cons a x -> Cons a (concat x v)
    
(* Lemma that concat is associative *)
val concat_assoc : xs:string -> ys:string -> zs:string -> 
    Lemma (concat (concat xs ys) zs = concat xs (concat ys zs))
let rec concat_assoc xs ys zs =
  match xs with
  | Empty -> ()
  | Cons a xs' -> concat_assoc xs' ys zs


(* Function definition of reverse *)
val reverse : string -> string
let rec reverse w = match w with
     | Empty -> Empty
     | Cons a x -> concat (reverse x) (Cons a Empty)

(* revLem1: can be automatically discharged *)
val revLem1 : a:symbol -> x:string -> 
    Lemma (reverse (Cons a x) = concat (reverse x) (Cons a Empty))
let revLem1 a x = 
    ()

(* Tips for playing with the proof checker:
   Try using "assert", to check the boundaries of what the solver can figure out.
   Use "let x = ... in" to bind new values, to help break down the problem.
   Use "admit()" to quit and report OK 
       (you're not finished until you've removed admit. *)

(* revLem2: need to provide an inductive proof *)
val revLem2 : u:string -> Lemma (concat u Empty = u)
let rec revLem2 u = match u with
    | Empty -> ()
    | Cons a x -> revLem2 x

(* Trickier lemma - you have to guide the proof search solver to the
   induction proof, and show it where to apply associativity *)
val reverseLemma : u:string -> v:string -> 
    Lemma (reverse (concat u v) ==  concat (reverse v) (reverse u))
let rec reverseLemma u v = 
    match u with
        | Empty -> revLem2 (reverse v)
        | Cons a x -> reverseLemma x v;
            concat_assoc (reverse v) (reverse x) (Cons a Empty);
            ()
