module Regex
(*
  See
   https://github.com/tchajed/regex-derivative/blob/master/RegularExpressions.fst
 *)

open FStar.Squash
open FStar.Classical
open FStar.List.Tot

let op_Plus_Plus = FStar.List.Tot.Base.append

(** The alphabet for strings *)
(* assume val sigma: t:Type0{hasEq t} *)
type sigma = | Z | O


type string : Type0 = list sigma

(** A language is traditionally a set of strings. In F*'s logic, the best way to
  express (possibly infinite) sets is as a predicate over strings; the
  interpretation will be that [forall (l:language) (s:string). l s] holds for exactly
  those strings in the language [l]. *)
type language = string -> GTot Type0

let is_in (s:string) (l:language) = l s

type regex =
  | Empty: regex (* Empty is the empty language, matching no strings. *)
  | Char : c:sigma -> regex
  | Or   : r1:regex -> r2:regex -> regex
  | Seq  : r1:regex -> r2:regex -> regex
  | Star : r:regex -> regex

(** eps is a derived regex that matches only the empty string. *)
let eps = Star Empty

val star : language -> (s:string) -> GTot Type0 (decreases %[s])
let rec star r = fun s ->
    s == [] \/
    (exists s1 s2. s == s1 ++ s2 /\ r s1 /\ star r s2)

(** The denotation of a regex is a language. These are the trusted semantics of
the regex type above. *)
val denotation: regex -> language
let rec denotation = function
  | Empty     -> fun s -> False
  | Char c    -> fun s -> s == [c]
  | Or r1 r2  -> fun s -> denotation r1 s \/ denotation r2 s
  | Seq r1 r2 -> fun s -> exists s1 s2. s == s1 ++ s2 /\ denotation r1 s1 /\ denotation r2 s2
  | Star r    -> fun s -> star (denotation r) s

(** Lemmas **)

(** Only the empty string is in the Kleene star of the empty language *)
let emptylang = (fun _ -> False)

val star_false: s:string -> star emptylang s -> Lemma (s == [])
let star_false s _ = ()

(* `eps` indeed represents the language consisting only of the empty string. *)
val eps_denotation: s:string -> Lemma (denotation eps s <==> s == [])
let eps_denotation s = ()

(** r(0+1) == r(1+0) **)
let r1 = Char Z `Or` Char O
let r2 = Char O `Or` Char Z

val lem1 : (s:string) -> Lemma (denotation r1 s <==> denotation r2 s)
let lem1 _ = ()


