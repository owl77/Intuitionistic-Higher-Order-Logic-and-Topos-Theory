# Intuitionistic-Higher-Order-Logic-and-Topos-Theory
Proof assistant based on the systems of intuitionistic higher order logic used in the foundational papers on logic and topos theory by Dana Scott, Michael Fourman, Gonzalo Reyes, Lawvere, etc. An alternative to dependent type theory.

The Ocaml file hol.ml (assuming only the modules List and String) builds the lexer, parser and basic operations on expressions from scratch. It is based on the presentation of higher-order logic in Fourman's paper The Logic of Topos (in Handbook of Mathematical Logic, ed. Barwise).

The next file proof.ml will include the implementation of a basic proof assistant for intuitionistic higher-order logic and our first goal is to prove all the logical lemmas in Fourman's paper (Theorem 3.5, Lemma 3.6, Lemma 3.10 ). 
