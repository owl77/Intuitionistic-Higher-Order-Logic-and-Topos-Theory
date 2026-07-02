
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

type proof_state = Proof of formula list * ((term * term) list) * formula list * (string list);;

(* proof itself, definitions, theorems assumed, log of axioms and rules used with parameters - to which we add the constants, variables and sorts*)

let init = Proof ([], [], [], []);;

let current_proof = ref init;;

let rec displayProof a = match a with 
                       x::y -> print_endline (printFormula x); displayProof y
                     |_ -> ();;

let seeProof () = match !current_proof with
 Proof(a,b,c,d) -> displayProof a ;;


let ax1 f g  = let aux = prop1 f g in match aux with
 Some v -> ( match !current_proof with
                 Proof (a,b,c,d) -> current_proof :=Proof (List.rev (v::(List.rev a))  ,b,c, List.rev (String.concat  " " [ "ax1" ; f; g]::(List.rev d) )         )  ; true   )
 |_ -> false;;



let modus_ponens n m proof = match proof with
 Proof (a,b,c,d) -> if n-1 > List.length a || m -1 > List.length a then None else let i = List.nth a (n -1) in let j = List.nth a (m -1) in match
i with
 BinaryOp ("->", u,v,_) -> if not (formulaEquality_wrap u j) then None else  Some (Proof (List.rev(v::(List.rev a)),b,c,
List.rev ((String.concat " " ["MP"; Int.to_string(n); Int.to_string(m)])::(List.rev d)  )))
|_ -> None;;
