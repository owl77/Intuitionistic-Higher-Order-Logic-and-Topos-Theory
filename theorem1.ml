
(* E q -> (q = q) Note: we use "=" to mean Fourman's equivalence *)

#use "proof.ml";;
#use "env.ml";;

 

(* proof *)

addHyp "E q";;
trans "p" "q" "z";;
sub 2 "q" "z";;
conj 3 1 ;;
inst 4 ;;
bi 5 7 ;;
addHyp "(q = q)" ;;
deduction 7 ;;
conj 8 8;;
mp 6 9;;
deduction 1;;


(*QED*)
seeEnv();;
seeProof();;

(*
Variables:   w:[]  q:[]  p:[]  z:[]  y:[]  x:a  

Constants:    

Propositional Constants:   T F

1. E q       addHyp E q
2. forall p (((p = q) <-> (p = z)) -> (q = z))       trans p q z
3. forall p (((p = q) <-> (p = q)) -> (q = q))       sub 2 q z
4. (forall p (((p = q) <-> (p = q)) -> (q = q)) & E q)       conj 3 1
5. (((q = q) <-> (q = q)) -> (q = q))       inst 4
6. ((((q = q) -> (q = q)) & ((q = q) -> (q = q))) -> (q = q))       bi 5 7
7. (q = q)       addHyp (q = q)
8. ((q = q) -> (q = q))       deduction 7
9. (((q = q) -> (q = q)) & ((q = q) -> (q = q)))       conj 8 8
10. (q = q)       mp 6 9
11. (E q -> (q = q))       deduction 1
*)
