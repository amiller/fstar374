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

val length : string -> nat
let rec length = function
    | Empty -> 0
    | Cons a x -> 1 + length x


(* Evaluating is fun. You can select an expression, send it to the evaluator. (C-c,C-s,C-e)
   Try selecting these:
   - length string1
   - length Empty
   - (3 + length Empty = length string1)
*)
let string1 = Cons SymA (Cons SymB (Cons SymC Empty))


(* Function definition of concatenation *)
val concat : string -> string -> string
let rec concat w v = match w with
    | Empty -> v
    | Cons a x -> Cons a (concat x v)

(* Function definition of reverse *)
val reverse : string -> string
let rec reverse w = match w with
     | Empty -> Empty
     | Cons a x -> concat (reverse x) (Cons a Empty)

(* revLem1: can be automatically discharged *)
val revLem1 : a:symbol -> x:string -> 
    Lemma (reverse (Cons a x) = concat (reverse x) (Cons a Empty))
let revLem1 a x = ()


(* Lemma that concat is associative.
  This one you need to spell out the inductive proof. *)
val concat_assoc : xs:string -> ys:string -> zs:string -> 
    Lemma (concat (concat xs ys) zs = concat xs (concat ys zs))
let rec concat_assoc xs ys zs =
  match xs with
  | Empty -> ()
  | Cons a xs' -> concat_assoc xs' ys zs


(* Now you need to start playing the game.

  Tips for playing with the proof checker:
   Try using "assert (x == y)" etc., to check the boundaries of what the solver can figure out.
   Use "let x = ... in" to bind new values, to help break down the problem.
   Use "admit()" to have the compiler move on to the next problem, accepting your word for now
       (you're not truly finished with your proof work until you've removed all the admits. *)

(* revLem2: need to provide an inductive proof *)
val revLem2 : u:string -> Lemma (concat u Empty = u)
let revLem2 u = admit()


(* Trickier lemma - you have to guide the proof search solver to the
   induction proof, and show it where to apply associativity *)
val reverseLemma : u:string -> v:string -> 
    Lemma (reverse (concat u v) ==  concat (reverse v) (reverse u))
let rec reverseLemma u v = admit()

(* Some exercises from the book *)

val lem_concat_length : u:string -> v:string -> Lemma (length (u `concat` v) == length u + length v)
let rec lem_concat_length u v = match u with
  | Empty -> ()
  | Cons a x -> lem_concat_length x v

(* Lemma 6(b) reverse length *)
val lem_ex6b (s:string) : Lemma( length s == length (reverse s) )
let rec lem_ex6b s = match s with
    | Empty -> () 
    | Cons a x -> 
      lem_concat_length (reverse x) (Cons a Empty);
      lem_ex6b x

(******
 Exercise 6: Swap function
 ******)

val swap : string -> string
let rec swap = function
 | Empty -> Empty
 | Cons a Empty -> Cons a Empty
 | Cons a (Cons b x) -> Cons b (Cons a (swap x))

(* Lemma 10(c): Prove that swap(reverse(w)) == reverse(swap(w)) *)
(* As the hint in the book suggests, this will involve several inductive definitions, including length and swap. *)
val lem_ex10c : (w:string) -> Lemma (requires ((length w) % 2 = 0)) (ensures swap (reverse w) == reverse (swap w))

(* First prove a simpler lemma about swap and concatenation *)
val lem_ex10c_help (u:string) (v:string) : Lemma 
                    (requires length u % 2 = 0 /\ length v % 2 = 0)
                    (ensures swap (u `concat` v) == swap u `concat` swap v)
let rec lem_ex10c_help u v = match u with
  | Empty -> ()
  | Cons a Empty -> ()
  | Cons a (Cons b x) -> lem_ex10c_help x v

let rec lem_ex10c w = match w with
   | Empty -> ()
   | Cons a Empty -> ()
   | Cons a (Cons b x) -> 
     if length w % 2 = 0 then (
       assert (length x % 2 = 0);
       let ab = Cons a (Cons b Empty) in
       let ba = Cons b (Cons a Empty) in
       (* Proof proceeds by calculating:
           swap(reverse(ab ++ x)) == swap(reverse x ++ ba)
                                  == swap(reverse x) ++ ab
                                  == reverse(swap x) ++ ab
                                  == reverse(ba ++ swap x)
                                  == reverse(swap(ab ++ x))
       This can be inserted as "assert" statements to check your progress.
        *)
       let s1 = swap (reverse w) in

       reverseLemma ab x;                 (* reverse <-> concat *)
       assert (s1 == swap(reverse x `concat` ba));

       lem_ex6b x;                        (* length <--> reverse: necessary for next line *)
       lem_ex10c_help (reverse x) ba;     (* concat <--> swap *)
       assert (s1 == swap(reverse x) `concat` ab);

       lem_ex10c x;                        (* inductive step *)
       assert (s1 == reverse(swap x) `concat` ab);

       reverseLemma ba (swap x);          (* reverse <-> concat *)
       ()
     ) else
       ()
