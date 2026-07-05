
(* axioms and rules of iHOL, Fourman p.1061 *)

#use "hol.ml";;

let prop1  h s = let phi = formula (lexer h) in let psi = formula (lexer s) in match phi with 
 Some phi_v -> (match psi with
                          Some psi_v ->  Some (BinaryOp ("->", phi_v, BinaryOp ("->", psi_v, phi_v, 0), 0)) 
                          |_ -> None)
|_ -> None;;



let prop2 h s t = let phi = formula (lexer h) in let psi = formula (lexer s) in let theta = formula (lexer t) in 
 match phi with
 Some phi_v -> (match psi with
                 Some psi_v -> (match theta with    
                                  Some theta_v ->Some( BinaryOp ("->", BinaryOp("->",phi_v, BinaryOp("->", psi_v, theta_v,0), 0),
 BinaryOp("->", BinaryOp("->",phi_v,psi_v,0), BinaryOp("->",phi_v, theta_v,0)       ,0)                    ,0)) 
                    |_ -> None)
                 |_ -> None)
|_ -> None;;
  
 let prop3 h s = let phi = formula (lexer h) in let psi = formula (lexer s) in match phi with
 Some phi_v -> (match psi with
                          Some psi_v ->  Some (BinaryOp ("->", BinaryOp ("&", phi_v, psi_v, 0), phi_v ,   0))  
                          |_ -> None)
|_ -> None;;


 let prop4 h s = let phi = formula (lexer h) in let psi = formula (lexer s) in match phi with
 Some phi_v -> (match psi with
                          Some psi_v ->  Some (BinaryOp ("->", BinaryOp ("&", phi_v, psi_v, 0), psi_v,    0))
                          |_ -> None)
|_ -> None;;

 let prop5 h s = let phi = formula (lexer h) in let psi = formula (lexer s) in match phi with
 Some phi_v -> (match psi with
                          Some psi_v ->  Some (BinaryOp ("->", phi_v, BinaryOp ("->", psi_v, BinaryOp("&",phi_v,psi_v,0), 0),    0))
                          |_ -> None)
|_ -> None;;

type proof_state = Proof of formula list * (formula list) * formula list * ((string list) list);;

(* proof itself, definitions, theorems assumed, log of axioms and rules used with parameters - to which we add the constants, variables and sorts*)

let init = Proof ([], [], [], []);;

let current_proof = ref init;;

let rec displayProof a b n  = match (a,b) with 
                       (x::y, z::w) -> let aux = String.concat " " z in print_endline (String.concat "" [Int.to_string(n); ". "; printFormula x; "       "; aux])  ; displayProof y w (n+1)
                     |_ -> ();;

let seeProof () = match !current_proof with
 Proof(a,b,c,d) -> displayProof a d 1 ;;

let log() = match !current_proof with
 Proof(a,b,c,d) -> d ;;

let seeHypotheses() = match !current_proof with
 Proof(a,b,c,d) -> d;;



let binRule prop f g name  = let aux = prop f g in match aux with
 Some v -> ( match !current_proof with
                 Proof (a,b,c,d) -> current_proof :=Proof (List.rev (v::(List.rev a))  ,b,c, List.rev ([name; f; g]::
(List.rev d) )         )  ; true   )
 |_ -> false;;

let triRule prop f g h name  = let aux = prop f g h in match aux with
 Some v -> ( match !current_proof with
                 Proof (a,b,c,d) -> current_proof :=Proof (List.rev (v::(List.rev a))  ,b,c, List.rev ([name; f; g; h]::
(List.rev d) )         )  ; true   )
 |_ -> false;;


let ax1 f g = binRule prop1 f g "ax1";;
let ax2 f g h = triRule prop2 f g h "ax2";;
let ax3 f g = binRule prop3 f g "ax3";;
let ax4 f g = binRule prop4 f g "ax4";;
let ax5 f g = binRule prop5 f g "ax5";;


let forall_pre f x = let aux1 = formula (lexer f) in let aux2 = term (lexer x) in match aux1 with
 Some a -> (match aux2 with
            Some ( Variable (q,w,e,r)) -> Some (BinaryOp("->", BinaryOp("&",  Binder ("forall",
 Variable (q,w,e,r), a,0), E (Variable (q,w,e,r),0),0), a,0   ))
             |_ -> None )
|_ -> None;;

let forall f x = binRule forall_pre f x "forall" ;;


let pre_ext f x y z = let f1 = formula(lexer f) in let x1 = term (lexer x) in let y1 = term (lexer y) in let z1 = term (lexer z) in
 match  f1,x1,y1,z1 with
  | Some f2, Some x2, Some y2, Some z2 ->  let f3 = setFreeForm_wrap f2 in let y3 = setFreeTerm_wrap y2 in let z3 = setFreeTerm_wrap z2 in 
if check_subForm f2 y3 && check_subForm f2 z3 then let aux1 = subForm f3 y3 x2 in let aux2 = subForm f3 z3 x2 in
let aux3 = BinaryOp ("&", aux1, Equiv (y3,z3,0), 0) in Some (BinaryOp ("->",aux3, aux2,0 )) else None
|_->None;;

let ext f x y z = let out = pre_ext f x y z in if not (out = None) then match !current_proof with
 Proof(a,b,c,d) -> (match out with
                        Some aux -> current_proof:= Proof (List.rev(aux::(List.rev a)),b,c,
List.rev (["ext"; f; x; y; z]::(List.rev d)  )); true         
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

let check_gen form = match form with
 BinaryOp ("->", a, b, _) -> (match a with
                               BinaryOp("&", c, d, _) -> (match d with 
                                                           E (Variable (v1,v2,v3,v4), _) -> 
let f = freeVarForm c in let v = getNames f in not (List.mem v1 v) 
                                                            |_-> false)
                              |_ -> false)
|_-> false;;

let pre_gen n proof = match proof with
   Proof (p1,p2,p3,p4) -> if n-1 > List.length p1 || n < 0 then None else if check_gen (List.nth p1 (n-1)) then
                                (match List.nth p1 (n-1) with                                               
                                 BinaryOp("->", BinaryOp("&", a, E(b,_),_), c,_) -> let aux =  (BinaryOp("->", a, Binder ("forall", b, c, 0),0) ) in 
Some (Proof (List.rev(aux::(List.rev p1)),p2,p3, List.rev (["gen";Int.to_string(n)]::(List.rev p4)  )))
                                 |_-> None      

) else None;;

let gen n = let aux = pre_gen n !current_proof in match aux with
 Some a -> current_proof := a; true
|None -> false;;

let addHyp f = let f1 = formula (lexer f) in match f1, !current_proof with
Some f2, Proof(a,b,c,d) -> current_proof:= Proof (List.rev(f2::(List.rev a)),b, c, List.rev (["addHyp";f]::(List.rev d)  ))
;true 
| _,_ ->false;;


(* write dependency functions to implement a |- b  => |- a -> b *) 

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
 Proof (_,_,_,a) -> if not (n < 1) && not (n > List.length a) then let aux = List.nth a (n -1) in  match List.nth aux 0 with
 "mp" -> List.concat [ dependencies (int_of_string (List.nth aux 1)) ; dependencies (int_of_string (List.nth aux 2))]
|"gen" ->  dependencies (int_of_string (List.nth aux 1))
| "sub"-> dependencies (int_of_string (List.nth aux 1))
| "addHyp" -> [n]
|"deduction" -> let d = dependencies (n-1) in let f x = not(x =  int_of_string(List.nth aux 1)) in 
List.filter f d  
| _ -> [] else [];; 
