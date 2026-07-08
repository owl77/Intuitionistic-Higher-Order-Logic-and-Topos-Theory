
(* |- F -> phi Theorem 3.5 (8) *)

#use "proof.ml";;

newVariable "y" "[]";;
newVariable "z" "[]";;
newVariable "p" "[]";;
newVariable "q" "[]";;

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

seeProof();;


