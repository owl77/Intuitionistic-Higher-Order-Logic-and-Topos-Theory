#use "proof.ml";;
#use "env.ml";;



addTheorem "(E q -> (q = q))"  ;;
addTheorem "(((z() -> z()) <-> y() ) <-> y() )" ;;


(* T = E y y() ,  |- T  Fourman  Th3.5 (7)  *)


addHyp "z()";;
deduction 1;;
comp "(z() -> z())" "y"   [];;
i "((z() -> z()) <-> y())"   "y" "q";;
i "y()" "y" "q";;
conj 5 3;;
inst 6;;
conj 4 3;;
inst 8;;
useTheorem 1;;
sub 10 "I y((z() -> z()) <-> y())" "q";;
mp 11 3;;
bi 9 45;;
l 13;;
mp 14 12;;
useTheorem 2;;
sub_equiv 15 16 9;;
bi 7 33;;
r 18;;
mp 19 17;;
ext "E p" "p" "q" "w" ;;
sub 21  "I y ((z() -> z()) <-> y())" "q";;
sub 22  "I y y()" "w";;
conj 3 20;;
mp 23 24;;

(* QED *)

seeEnv();;
seeProof();;

(*

Variables:   w:[]  q:[]  p:[]  z:[]  y:[]  x:a  

Constants:    

Propositional Constants:   T F

1. z()       addHyp z()
2. (z() -> z())       deduction 1
3. E I y ((z() -> z()) <-> y())       comp (z() -> z()) y
4. forall q ((q = I y ((z() -> z()) <-> y())) <-> forall y (((z() -> z()) <-> y()) <-> (y = q)))       i ((z() -> z()) <-> y()) y q
5. forall q ((q = I y y()) <-> forall y (y() <-> (y = q)))       i y() y q
6. (forall q ((q = I y y()) <-> forall y (y() <-> (y = q))) & E I y ((z() -> z()) <-> y()))       conj 5 3
7. ((I y ((z() -> z()) <-> y()) = I y y()) <-> forall y (y() <-> (y = I y ((z() -> z()) <-> y()))))       inst 6
8. (forall q ((q = I y ((z() -> z()) <-> y())) <-> forall y (((z() -> z()) <-> y()) <-> (y = q))) & E I y ((z() -> z()) <-> y()))       conj 4 3
9. ((I y ((z() -> z()) <-> y()) = I y ((z() -> z()) <-> y())) <-> forall y (((z() -> z()) <-> y()) <-> (y = I y ((z() -> z()) <-> y()))))       inst 8
10. (E q -> (q = q))       useTheorem 1
11. (E I y ((z() -> z()) <-> y()) -> (I y ((z() -> z()) <-> y()) = I y ((z() -> z()) <-> y())))       sub 10 I y((z() -> z()) <-> y()) q
12. (I y ((z() -> z()) <-> y()) = I y ((z() -> z()) <-> y()))       mp 11 3
13. (((I y ((z() -> z()) <-> y()) = I y ((z() -> z()) <-> y())) -> forall y (((z() -> z()) <-> y()) <-> (y = I y ((z() -> z()) <-> y())))) & (forall y (((z() -> z()) <-> y()) <-> (y = I y ((z() -> z()) <-> y()))) -> (I y ((z() -> z()) <-> y()) = I y ((z() -> z()) <-> y()))))       bi 9 45
14. ((I y ((z() -> z()) <-> y()) = I y ((z() -> z()) <-> y())) -> forall y (((z() -> z()) <-> y()) <-> (y = I y ((z() -> z()) <-> y()))))       l 13
15. forall y (((z() -> z()) <-> y()) <-> (y = I y ((z() -> z()) <-> y())))       mp 14 12
16. (((z() -> z()) <-> y()) <-> y())       useTheorem 2
17. forall y (y() <-> (y = I y ((z() -> z()) <-> y())))       sub_equiv 15 16 9
18. (((I y ((z() -> z()) <-> y()) = I y y()) -> forall y (y() <-> (y = I y ((z() -> z()) <-> y())))) & (forall y (y() <-> (y = I y ((z() -> z()) <-> y()))) -> (I y ((z() -> z()) <-> y()) = I y y())))       bi 7 33
19. (forall y (y() <-> (y = I y ((z() -> z()) <-> y()))) -> (I y ((z() -> z()) <-> y()) = I y y()))       r 18
20. (I y ((z() -> z()) <-> y()) = I y y())       mp 19 17
21. ((E q & (q = w)) -> E w)       ext E p p q w
22. ((E I y ((z() -> z()) <-> y()) & (I y ((z() -> z()) <-> y()) = w)) -> E w)       sub 21 I y ((z() -> z()) <-> y()) q
23. ((E I y ((z() -> z()) <-> y()) & (I y ((z() -> z()) <-> y()) = I y y())) -> E I y y())       sub 22 I y y() w
24. (E I y ((z() -> z()) <-> y()) & (I y ((z() -> z()) <-> y()) = I y y()))       conj 3 20
25. E I y y()       mp 23 24

 *)
