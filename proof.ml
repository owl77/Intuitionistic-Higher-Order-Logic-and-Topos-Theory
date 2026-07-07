
(* axioms and rules of iHOL, Fourman p.1061 - but adapted to natural deduction style

rules:

mp n m (modus ponens)
deduction n   a |- b   => |- a -> b
conj n m      a, b    =>  (a & b)
r n     (a & b)   =>  a
l n  (a & b) =>  b
gen n   Ex -> a  => forall x a   (x not free in dependencies of Ex -> a)
sub n  a  => a [ t /x]
inst n   forall x a & Et   =>  a[t /x] 

axioms:

ext
trans
I
comp
pred

addHyp
 *)

#use "hol.ml";;

type proof_state = Proof of formula list * (formula list) * formula list * ((string list) list);;

(* proof itself, definitions, theorems assumed, log of axioms and rules used with parameters - to which we add the constants, variables and sorts*)

let init = Proof ([], [], [], []);;

let current_proof = ref init;;


let update_proof form strings = match !current_proof with
 Proof(a,b,c,d) -> current_proof := Proof (List.append a [form],b,c, List.append d [strings]);;

let rec displayProof a b n  = match (a,b) with 
                       (x::y, z::w) -> let aux = String.concat " " z in 
print_endline (String.concat "" [Int.to_string(n); ". "; printFormula x false false; "       "; aux])  ; displayProof y w (n+1)
                     |_ -> ();;

let seeProof () = match !current_proof with
 Proof(a,b,c,d) -> displayProof a d 1 ;;

let log() = match !current_proof with
 Proof(a,b,c,d) -> d ;;

let seeTheorems() = match !current_proof with
 Proof(a,b,c,d) -> b;;

let getForms () = match !current_proof with
 Proof(a,_,_,_) -> a;;

let range n = not (n < 1) && not (n > List.length (getForms () )) ;;

let getForm n = if range n then match !current_proof with
 Proof(a,_,_,_) -> Some (List.nth a (n-1))  else None;;




let binRule prop f g name  = let aux = prop f g in match aux with
 Some v -> ( match !current_proof with
                 Proof (a,b,c,d) -> current_proof :=Proof (List.append a [v]  ,b,c, List.append d [[name; f; g]])  ; true   )
 |_ -> false;;



let pre_ext f x y z = let f1 = formula(lexer f) in let x1 = term (lexer x) in let y1 = term (lexer y) in let z1 = term (lexer z) in
 match  f1,x1,y1,z1 with
  | Some f2, Some x2, Some y2, Some z2 ->  let f3 = setFreeForm_wrap f2 in let y3 = setFreeTerm_wrap y2 in let z3 = setFreeTerm_wrap z2 in 
if check_subForm f2 y3 && check_subForm f2 z3 then let aux1 = subForm f3 y3 x2 in let aux2 = subForm f3 z3 x2 in
let aux3 = BinaryOp ("&", aux1, Equiv (y3,z3,0), 0) in Some (BinaryOp ("->",aux3, aux2,0 )) else None
|_->None;;

let ext f x y z = let out = pre_ext f x y z in if not (out = None) then match !current_proof with
 Proof(a,b,c,d) -> (match out with
                        Some aux -> current_proof:= Proof (List.append a [aux],b,c,
List.append d [["ext"; f; x; y; z]]); true         
                      |_ -> false) else false;;

let pre_trans x y z = let x1 = term (lexer x) in let y1 = term (lexer y) in let z1 = term (lexer z) in match x1,y1,z1 with
 Some (Variable(a,b,c,d)), Some (Variable(a1,b1,c1,d1)), Some (Variable(a2,b2,c2,d2)) -> if sortEquals(b,b1) && sortEquals(b,b2) then
let left = BinaryOp("<->", Equiv (Variable(a,b,c,d), Variable(a1,b1,c1,d1),0),
Equiv (Variable(a,b,c,d), Variable(a2,b2,c2,d2), 0) , 0) in let right = Equiv(Variable(a1,b1,c1,d1), Variable(a2,b2,c2,d2),0) in
Some (Binder("forall", Variable(a,b,c,d), BinaryOp("->", left,right,0),0 )) else None
 | _ -> None;;


let trans x y z = let aux = pre_trans x y z in match !current_proof, aux with
 Proof(a,b,c,d), Some e -> current_proof := Proof (List.append a [e], b, c, List.append d [["trans"; x; y; z  ]]);true 
|_, _ -> false;;


let pre_I f x y = let f1 = formula(lexer f) in let x1 = term (lexer x) in let y1 = term (lexer y) in match f1,x1,y1 with
 Some f2, Some(Variable(a,b,c,d)), Some(Variable (a1,b1,c1,d1)) -> if sortEquals(b,b1) then let left = Equiv(Variable(a1,b1,c1,d1), I (Variable(a,b,c,d), f2,0),0) in let
right = Binder ("forall", Variable(a,b,c,d), BinaryOp ("<->", f2, Equiv (Variable(a,b,c,d), Variable(a1,b1,c1,d1),0), 0) ,0) in
Some (Binder ("forall",Variable (a1,b1,c1,d1), BinaryOp ("<->", left, right, 0),0)) else None
|_,_,_ -> None;;


let i f x y = let aux = pre_trans f x y in match !current_proof, aux with
 Proof(a,b,c,d), Some e -> current_proof := Proof (List.append a [e], b, c, List.append d [["i";f;  x; y;  ]]);true
|_, _ -> false;;

let pre_comp_0 f y = let f1 = formula (lexer f)  in let y1 = term (lexer y) in match f1,y1 with
Some f2, Some(Variable(a1,b1,c1,d1)) -> if sortEquals(b1, RelSort []) then
Some ( E ( I( Variable(a1,b1,c1,d1), BinaryOp("<->", f2, App (Variable(a1,b1,c1,d1),[],0)         ,0 ),0 ),0 )  ) else None 
|_,_ -> None;;

let comp_0 f y = let aux = pre_comp_0 f y in match !current_proof, aux with
 Proof(a,b,c,d), Some e -> current_proof := Proof (List.append a [e], b, c, List.append d [["comp_0"; f; y ]]);true
|_, _ -> false;;

(* can do general comp with an argument list of strings *)

let modus_ponens n m proof = match proof with
 Proof (a,b,c,d) -> if n-1 > List.length a || m -1 > List.length a then None else let i = List.nth a (n -1) in let j = List.nth a (m -1) in match
i with
 BinaryOp ("->", u,v,_) -> if not (formulaEquality_wrap u j) then None else  Some (Proof (List.rev(v::(List.rev a)),b,c,
List.rev (["mp"; Int.to_string(n); Int.to_string(m)]::(List.rev d)  )))
|_ -> None;;

let mp n m = let aux = modus_ponens n m !current_proof in match aux with
 Some a -> current_proof := a;true
|_ -> false;;


let pre_sub n t x proof =  let v = term (lexer x) in let s = term (lexer t) in match v with
 Some Variable (u1,u2,u3,u4) -> (match s with 
                       Some i ->  (match proof with
                                      Proof (a,b,c,d) -> if n-1 > List.length a then None else 
      let f = setFreeForm_wrap(List.nth a (n-1)) in if check_subForm f i then 
                                 let aux = subForm f i (Variable (u1,u2,u3,u4)) in     
                          Some (Proof (List.rev(aux::(List.rev a)),b,c,
List.rev (["sub";Int.to_string(n);x;t]::(List.rev d)  ))) else None  )
                       |_ -> None)
|_-> None;;


let sub n t x = let aux = pre_sub n t x !current_proof in match aux with 
 Some a -> current_proof := a; true
|_ -> false;;


let addHyp f = let f1 = formula (lexer f) in match f1, !current_proof with
Some f2, Proof(a,b,c,d) -> current_proof:= Proof (List.rev(f2::(List.rev a)),b, c, List.rev (["addHyp";f]::(List.rev d)  ))
;true 
| _,_ ->false;;


let deduction n = match !current_proof with
 Proof (p1,p2,p3,p4) -> if not (n = List.length p1  -1) && not(n > List.length p1) && 
List.nth (List.nth p4 (n-1)) 0  = "addHyp" then
let aux =  List.nth p1 (n-1) in let aux2 = BinaryOp ("->", aux, List.nth p1 ((List.length p1) - 1) , 0) in
 current_proof := Proof(List.append p1 [aux2], p2, p3, List.append p4 [["deduction"; Int.to_string(n)]]); true
 else false;;

let undo () = match !current_proof with
 Proof (a,b,c,d) -> if List.length a > 0 then  (current_proof := Proof (List.take ((List.length a) -1)  a , b , c , List.take ((List.length d) -1) d );true)
else false;;

let rec dependencies n = match !current_proof with
 Proof (_,_,_,a) -> if range n then let aux = List.nth a (n -1) in let prefix = List.nth aux 0 in
if List.mem prefix ["mp"; "conj"] then 
 List.concat [ dependencies (int_of_string (List.nth aux 1)) ; dependencies (int_of_string (List.nth aux 2))] else
if List.mem prefix ["gen"; "sub"; "inst"; "l"; "r";"bi"] then  dependencies (int_of_string (List.nth aux 1)) else
if prefix = "addHyp" then [n] else if
prefix = "deduction" then let d = dependencies (n-1) in let f x = not(x =  int_of_string(List.nth aux 1)) in 
List.filter f d else [] else [];;


let rec check_var_dependencies v list = match list with
x::y -> let aux = getForm x in (match aux with
Some f -> let aux2 = freeVarForm f in  not (varMember v aux2) && check_var_dependencies v y
|_ -> false) 
|_ -> true;;


let gen n = if range n then let d = dependencies n in  (match getForm n with
              Some ( BinaryOp ("->", E (v,p),  a,_)  ) -> if check_var_dependencies v d then let aux = Binder("forall", v, a, 0) in
                            update_proof aux ["gen"; Int.to_string n]; true else false
              |_ -> false) 
 else false;;


let inst n = if range n then match getForm n with
 Some(BinaryOp ("&", Binder ("forall", v, a,_), E (b,_),_ ) ) -> let f = setFreeForm_wrap a in if check_subForm f b && 
sortEquals (getSort v , getSort b) then   let aux = subForm a b v in update_proof aux ["inst"; Int.to_string n];true
else false
|_ -> false
 else false;; 

let conj n m = if range n && range m then let aux1 = getForm n in let aux2 = getForm m in match aux1,aux2 with
 Some l, Some r -> let aux3 = BinaryOp("&", l, r, 0) in update_proof aux3 ["conj"; Int.to_string n; Int.to_string m ]; true
|_ -> false
else false;;

let l n = if range n then let aux = getForm n in match aux with
 Some (BinaryOp("&", a, b,_   )) -> update_proof a ["l"; Int.to_string n];true
|_-> false
else false;;

let r n = if range n then let aux = getForm n in match aux with
 Some (BinaryOp("&", a, b,_   )) -> update_proof b ["r" ; Int.to_string n];true
|_-> false
else false;;


(*missing pred axiom *)

(* expand out <-> *)

let bi_exp f = match f with
BinaryOp ("<->",a,b,p) -> BinaryOp("&", BinaryOp("->", a,b,p), BinaryOp("->", b, a, p), p)
|_ -> f;;

let bi n pos = if range n then let aux = getForm n in match aux with
 Some f -> let aux2 = setOpPosForm_wrap f "<->" in let aux3 = transformF (aux2,bi_exp, pos) in update_proof aux3 ["bi"; Int.to_string n; Int.to_string pos];true
|_ -> false
else false;;  
