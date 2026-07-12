
#use "proof.ml";;
#use "env.ml";;

addHyp "((z() -> z()) -> y())";;
addHyp "z()";;
deduction 2;;
mp 1 3;;
deduction 1;;
addHyp "(z() -> z())";;
addHyp "y()";;
deduction 6;;
deduction 7;;
conj 5 9;;
make_equiv 10;;

(* QED *)

seeEnv();;
seeProof();;

(* 
Variables:   w:[]  q:[]  p:[]  z:[]  y:[]  x:a  

Constants:    

Propositional Constants:   T F


1. ((z() -> z()) -> y())       addHyp ((z() -> z()) -> y())
2. z()       addHyp z()
3. (z() -> z())       deduction 2
4. y()       mp 1 3
5. (((z() -> z()) -> y()) -> y())       deduction 1
6. (z() -> z())       addHyp (z() -> z())
7. y()       addHyp y() 
8. ((z() -> z()) -> y())       deduction 6
9. (y() -> ((z() -> z()) -> y()))       deduction 7
10. ((((z() -> z()) -> y()) -> y()) & (y() -> ((z() -> z()) -> y())))       conj 5 9
11. (((z() -> z()) -> y()) <-> y())       make_equiv 10

*)
