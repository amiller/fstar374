   This is a presentation in F* of some theory about decidable
   languages, and Deterministic Finite-state Automata (DFAs).

   It is intended as a supplement to a Models of Computation course,
   that provides a gentle introduction to mechanized proofs.

   - _[Strings.fst](Strings.fst):_ (easy)
     Define strings as inductive types, and give some simple
     inductive proofs.
     The difficulty is similar to Section 4 in the F* tutorial[2], and
     includes some lemmas and exercises from Ch. 1 of Models of
     Computation [1].

   - _[DFAs.fst](DFAs.fst):_ (medium)
     Defines DFAs and gives a few inductive proofs as well as
     the product construction for intersection of languages.
     Corresponds to Ch. 3 of Models of Computation [1].

   - _[MyhillNerode.fst](MyhillNerode.fst):_ (hard)
      This gives a presentation of the Myhill Nerode theorem, based
      on the notions of "fooling sets" Ch.3 [1] and "classifiers" [1].

   [1] Models of Computation. Jeff Erickson.
   http://jeffe.cs.illinois.edu/teaching/algorithms/models/all-models.pdf

   [2] F* Tutorial. https://www.fstar-lang.org/tutorial/

   [3] Regular Language Representations in the Constructive
   Type Theory of Coq
   Christian Doczkal, Gert Smolka
   https://hal.archives-ouvertes.fr/hal-01832031/document
