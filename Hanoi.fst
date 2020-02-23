module Hanoi
(* Towers of Hanoi in F* *)

(*
Let’s define a data structure for the board.
*)


open DFAs
open FStar.Classical
open FStar.Fin
open FStar.List.Tot
module S = FStar.Seq

(* Give some basic types for the configuration of a Hanoi puzzle *)
type disc = nat
type pole = list disc
type board = pole * pole * pole


(* Define the valid moves as axioms. *)
assume val canMove : board -> board -> Type0

(* We can add a disc to a pole only if the pole is empty, or 
   if the disc is smaller than the current top. *)
let canAdd (d:disc) (p:pole) : Type0 =
  match p with
  | [] -> True
  | (top :: rest) -> (d < top)		

(* Define three pick moves (the other three can be derived) *)
assume val ax0 : forall d p q z. canAdd d p ==> canAdd d q ==> canMove (d::p, q, z) (p, d::q, z)
assume val ax1 : forall d p q z. canAdd d p ==> canAdd d z ==> canMove (d::p, q, z) (p, q, d::z)
assume val ax3 : forall d p q z. canAdd d q ==> canAdd d z ==> canMove (p, d::q, z) (p, q, d::z)

(* Transitive *)
assume val ax_tr : forall b0 b1 b2. canMove b0 b1 ==> canMove b1 b2 ==> canMove b0 b2
(* Symmetric *)
assume val ax_sy : forall b0 b1. canMove b0 b1 ==> canMove b1 b0
(* Reflexive *)
assume val ax_re : forall b0. canMove b0 b0


(* Define sequence [0..n-1] *)
val seq : nat -> list nat

let rec seq' (n:nat) (i:nat) = if n = 0 then [] else i :: seq' (n-1) (i+1) 
let seq n : list nat = seq' n 0


(* Define the Towers of Hanoi puzzle. 
  Your challenge is to instantiate this proposition! *)
val hanoiTheorem : (n:nat) -> Lemma (canMove (seq n, [], []) ([], [], seq n))





(* SOLUTION HERE *)

(* A first step: We only have 3 of the 6 moves given. Also, they are in the "forall" form, which is hard to explicitly work wtih. So lets define all 6 as lemmas we can reference. *)
let lem_0 d p q r : Lemma (requires canAdd d p /\ canAdd d q) (ensures canMove (d::p, q, r) (p, d::q, r)) = ax0
let lem_1 d p q r : Lemma (requires canAdd d p /\ canAdd d r) (ensures canMove (d::p, q, r) (p, q, d::r)) = ax1
let lem_2 d p q r : Lemma (requires canAdd d q /\ canAdd d p) (ensures canMove (p, d::q, r) (d::p, q, r)) = lem_0 d p q r; ax_sy
let lem_3 d p q r : Lemma (requires canAdd d q /\ canAdd d r) (ensures canMove (p, d::q, r) (p, q, d::r)) = ax3
let lem_4 d p q r : Lemma (requires canAdd d r /\ canAdd d p) (ensures canMove (p, q, d::r) (d::p, q, r)) = lem_1 d p q r; ax_sy
let lem_5 d p q r : Lemma (requires canAdd d r /\ canAdd d q) (ensures canMove (p, q, d::r) (p, d::q, r)) = lem_3 d p q r; ax_sy

(* The other axioms in explicit form too *)
let lem_tr b0 b1 b2 : Lemma (requires canMove b0 b1 /\ canMove b1 b2) (ensures canMove b0 b2) = ax_tr
let lem_re b0 : Lemma (canMove b0 b0) = ax_re

(* Second step: 

  We can't easily do induction on the axioms as defined in the problem.
  So we need to come up with our own inductive definition of "Moves".
 *)
 
let nth_pole (b:board) (i:fin 3) = 
  let (x,y,z) = b in 
  match i with 0 -> x | 1 -> y | 2 -> z

let with_pole (b:board) (x:pole) (i:fin 3) = 
  let (p,q,r) = b in 
    match i with 0 -> (x,q,r) | 1 -> (p,x,r) | 2 -> (p,q,x)

let canPick (b:board) (i: fin 3) (j: fin 3) = 
    if i = j then False else
    let p = nth_pole b i in
    let q = nth_pole b j in
      match p with [] -> False
      | d::p' -> canAdd d p' /\ canAdd d q

let pick i j (b:board{canPick b i j}) : board =
  let (d::p') = nth_pole b i in
  let q = nth_pole b j in
  with_pole (with_pole b p' i) (d::q) j

type move = fin 3 * fin 3

let rec validMove (ms: list move) (b0:board) (b1:board) =
  let (p, q, r ) = b0 in
  let (p',q',r') = b1 in
  match ms with
  | [] -> b0 == b1
  | (i,j) :: ms' -> canPick b0 i j /\ validMove ms' (pick i j b0) b1

(* Valid moves are consistent with the logic definition *)
let lemValMove (i:fin 3) (j:fin 3) (b0:board) : 
  Lemma (requires canPick b0 i j /\ validMove [(i,j)] b0 (pick i j b0))
  (ensures canMove b0 (pick i j b0)) = 
  match (i,j) with
  | (0,1) -> ax0
  | (0,2) -> ax1
  | (1,0) -> let (p, d::q, r) = b0 in lem_2 d p q r
  | (1,2) -> ax3
  | (2,0) -> let (p, q, d::r) = b0 in lem_4 d p q r
  | (2,1) -> let (p, q, d::r) = b0 in lem_5 d p q r

let rec lemValMoves ms b0 b1 : 
  Lemma (requires validMove ms b0 b1) 
        (ensures canMove b0 b1) =
  match ms with 
  | [] -> ax_re
  | (i,j)::ms' -> lemValMove i j b0; 
                lemValMoves ms' (pick i j b0) b1; 
                lem_tr b0 (pick i j b0) b1


(* Main idea 1: We can permute the moves, and it applies to permuted boards. *)

let mmap (f : fin 3 -> fin 3) (moves: list (fin 3 * fin 3)) = 
  map (fun (i,j) -> (f i, f j)) moves

(* Cyclic shift 1 *)
val shift_n (n:fin 3) : fin 3
let shift_n = function
  | 0 -> 1
  | 1 -> 2
  | 2 -> 0

let shift_b (b:board) : board = let (p,q,r) = b in (r,p,q)

let lemShift i j (b0:board) : Lemma (requires canPick b0 i j)
  (ensures pick (shift_n i) (shift_n j) (shift_b b0) ==
           shift_b (pick i j b0)) =
  ()


let rec lemShiftMap ms b0 b1 : Lemma (requires validMove ms (shift_b (shift_b b0)) (shift_b (shift_b b1)))
  (ensures validMove (mmap shift_n ms) b0 b1) =
  match ms with 
  | [] -> ()
  | (i,j)::ms' -> lemShift i j (shift_b (shift_b b0));
                lemShiftMap ms' (shift_b (pick i j (shift_b (shift_b b0)))) b1

(* Swap first two *)
val swap_n (n:fin 3) : fin 3
let swap_n = function
  | 0 -> 1
  | 1 -> 0
  | 2 -> 2
let swap_b (b:board) : board = let (p,q,r) = b in (q,p,r)
let lemSwap i j (b0:board) : Lemma (requires canPick b0 i j)
  (ensures canPick (shift_b b0) (shift_n i) (shift_n j)) =
  ()

let rec lemSwapMap ms b0 b1 : Lemma (requires validMove ms (swap_b b0) (swap_b b1))
  (ensures validMove (mmap swap_n ms) b0 b1) =
  match ms with 
  | [] -> ()
  | (i,j)::ms' -> lemSwap i j (swap_b b0);
                lemSwapMap ms' (swap_b (pick i j (swap_b b0))) b1

(* Concatenation of moves *)
let rec lem_cat ms01 ms12 b0 b1 b2 : Lemma (requires validMove ms01 b0 b1 /\ validMove ms12 b1 b2) (ensures validMove (ms01 @ ms12) b0 b2) = 
  match ms01 with
  | [] -> ()
  | (i,j)::ms -> lem_cat ms ms12 (pick i j b0) b1 b2


(* Main idea 2: Self reduction *)

(* Bound all the elements in the board *)
let rec pole_lt (n:nat) (p:pole) = match p with [] -> True | (d::p') -> d < n /\ pole_lt n p'
let board_lt (n:nat) (b:board) = let (x,y,r) = b in 
  pole_lt n x /\ pole_lt n y /\ pole_lt n r

(* Appending tiles to some pile in the board *)
let add_p d (b:board) = let (p,q,r) = b in (p @ [d], q, r)
let add_r d (b:board) = let (p,q,r) = b in (p, q, r @ [d])

(* Reduction lemma: if all the tiles are < n, then we can add n to the
   bottom of a pile, and the reduction still holds. *)
let lem_addp' (n:nat) i j (b0:board {board_lt n b0}) :
  Lemma (requires canPick b0 i j) (ensures pick i j (add_p n b0) == add_p n (pick i j b0)) = ()
let lem_addr' (n:nat) i j (b0:board {board_lt n b0}) :
  Lemma (requires canPick b0 i j) (ensures pick i j (add_r n b0) == add_r n (pick i j b0)) = ()


let rec lem_addp (n:nat) (ms:list move) (b0:board {board_lt n b0}) (b1:board {board_lt n b1}):
  Lemma (requires validMove ms b0 b1)
        (ensures validMove ms (add_p n b0) (add_p n b1)) =
    match ms with 
    | [] -> ()
    | (i,j)::ms' -> lem_addp' n i j b0; lem_addp n ms' (pick i j b0) b1
let rec lem_addr (n:nat) (ms:list move) (b0:board {board_lt n b0}) (b1:board {board_lt n b1}):
  Lemma (requires validMove ms b0 b1)
        (ensures validMove ms (add_r n b0) (add_r n b1)) =
    match ms with 
    | [] -> ()
    | (i,j)::ms' -> lem_addr' n i j b0; lem_addr n ms' (pick i j b0) b1


(* Adding a tile preserves the pole bound *)
let rec lem_n' (b:nat) (n:nat) (i:nat) : Lemma (ensures n + i <= b ==> pole_lt b (seq' n i)) (decreases n) = 
 match n with 
 | 0 -> () 
 | _ -> lem_n' b (n-1) (i+1)

let rec lem_seq (n:nat) (i:nat) : Lemma (requires n > 0) (ensures seq' (n-1) i @ [n+i-1] == seq' n i) =
    match n with 1 -> () 
    | _ -> lem_seq (n-1) (i+1)

let rec hanoiMoves (n:nat) : (ms:list move {validMove ms (seq n, [], []) ([], [], seq n)}) =
  match n with
  | 0 -> []
  | _ ->
    lem_n' (n-1) (n-1) 0;
    lem_n' (n) (n-1) 0;
    assert (pole_lt n [n-1]);
    let (b0:board {board_lt (n-1) b0}) = (seq (n-1), [], []) in
    let (b1:board {board_lt (n-1) b1}) = ([], seq (n-1), []) in
    let (b2:board {board_lt (n-1) b2}) = ([], [], seq (n-1)) in

    // Self reduced instance
    let ms' = hanoiMoves (n-1) in

    // b0 to b1
    let ms01a = mmap shift_n ms' in
    lemShiftMap ms' b1 b0;
    lemSwapMap (mmap shift_n ms') b0 b1;
    let ms01 = mmap swap_n (mmap shift_n ms') in
    // assert (validMove ms01 b0 b1);

    // b1 to b2
    lemSwapMap ms' b1 (swap_b b2);
    let ms12 = mmap swap_n ms' in
    // assert (validMove ms12 b1 b2);

    // b0a to b2b
    let b0p = add_p (n-1) b0 in
    let b1p = add_p (n-1) b1 in
    let b1r = add_r (n-1) b1 in
    let b2r = add_r (n-1) b2 in
    lem_addp (n-1) ms01 b0 b1;
    // assert (validMove [(0,2)] b1p b1r);
    lem_addr (n-1) ms12 b1 b2;
    lem_cat [(0,2)] ms12 b1p b1r b2r;
    // assert (validMove ([(0,2)] @ ms12) b1p b2r);
    lem_cat ms01 ([(0,2)] @ ms12) b0p b1p b2r;
    //assert (validMove (ms01 @ [(0,2)] @ ms12) b0p b2r);
    lem_seq n 0;
    //assert (add_r (n-1) b2 == ([], [], seq n));
    ms01 @ [(0,2)] @ ms12
    
let hanoiTheorem n = 
    let ms = hanoiMoves n in lemValMoves ms (seq n, [], []) ([], [], seq n)
