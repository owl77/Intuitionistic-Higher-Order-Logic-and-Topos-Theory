
(* |- F -> phi Theorem 3.5 (8) *)

#use "proof.ml";;
#use "env.ml";;

addTheorem "( E q -> (q = q))";; 

(* proof *)

addHyp "forall y y()";;
comp "p()" "y" [];;
conj 1 2;;
inst 3;;
i "(p() <-> y())" "y" "z";;
conj 5 2;;
inst 6;;
bi 7 33;;
l 8;;
useTheorem 1;;
sub 10 "I y (p() <-> y())" "q";;
mp 11 2;;
mp 9 12;;
conj 13 2;;
inst 14;;
bi 15 27;; 
r 16;;
mp 17 12;;
bi 18 11;;
r 19;;
mp 20 4;;
deduction 1;;

(*QED*)
seeEnv();;
seeProof();;

(*
Variables:   w:[]  q:[]  p:[]  z:[]  y:[]  x:a  

Constants:    

Propositional Constants:   T F

1. forall y y()       addHyp forall y y()
2. E I y (p() <-> y())       comp p() y
3. (forall y y() & E I y (p() <-> y()))       conj 1 2
4. I y (p() <-> y())()       inst 3
5. forall z ((z = I y (p() <-> y())) <-> forall y ((p() <-> y()) <-> (y = z)))       i (p() <-> y()) y z
6. (forall z ((z = I y (p() <-> y())) <-> forall y ((p() <-> y()) <-> (y = z))) & E I y (p() <-> y()))       conj 5 2
7. ((I y (p() <-> y()) = I y (p() <-> y())) <-> forall y ((p() <-> y()) <-> (y = I y (p() <-> y()))))       inst 6
8. (((I y (p() <-> y()) = I y (p() <-> y())) -> forall y ((p() <-> y()) <-> (y = I y (p() <-> y())))) & (forall y ((p() <-> y()) <-> (y = I y (p() <-> y()))) -> (I y (p() <-> y()) = I y (p() <-> y()))))       bi 7 33
9. ((I y (p() <-> y()) = I y (p() <-> y())) -> forall y ((p() <-> y()) <-> (y = I y (p() <-> y()))))       l 8
10. (E q -> (q = q))       useTheorem 1
11. (E I y (p() <-> y()) -> (I y (p() <-> y()) = I y (p() <-> y())))       sub 10 I y (p() <-> y()) q
12. (I y (p() <-> y()) = I y (p() <-> y()))       mp 11 2
13. forall y ((p() <-> y()) <-> (y = I y (p() <-> y())))       mp 9 12
14. (forall y ((p() <-> y()) <-> (y = I y (p() <-> y()))) & E I y (p() <-> y()))       conj 13 2
15. ((p() <-> I y (p() <-> y())()) <-> (I y (p() <-> y()) = I y (p() <-> y())))       inst 14
16. (((p() <-> I y (p() <-> y())()) -> (I y (p() <-> y()) = I y (p() <-> y()))) & ((I y (p() <-> y()) = I y (p() <-> y())) -> (p() <-> I y (p() <-> y())())))       bi 15 27
17. ((I y (p() <-> y()) = I y (p() <-> y())) -> (p() <-> I y (p() <-> y())()))       r 16
18. (p() <-> I y (p() <-> y())())       mp 17 12
19. ((p() -> I y (p() <-> y())()) & (I y (p() <-> y())() -> p()))       bi 18 11
20. (I y (p() <-> y())() -> p())       r 19
21. p()       mp 20 4
22. (forall y y() -> p())       deduction 1
*)
