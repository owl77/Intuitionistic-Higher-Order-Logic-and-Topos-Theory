
(*lexer*)

let ssub s n m = String.sub s n (m-n);;
let suf s n = let l = String.length s in ssub s n l;;

let rec space1 s = if String.length s < 2 then s else if (ssub s 0 2) = "  " then space1 (suf s 1) else
String.concat "" [ssub s 0 1; space1 (suf s 1)] ;;


let rec spaceremove s = if s = "" then s else if s.[0] = ' ' then spaceremove (suf s 1) else String.concat "" [ssub s 0 1; spaceremove (suf s 1)];;

let rec rectify s = if String.length s < 2 then s else if List.mem s.[0] ['(';')';'.';'>';']'; '['; ':'; '='; 'E'; 'I'; '&'; ','] && not (s.[1]=' ') then
String.concat "" [ssub s 0 1;" ";rectify (suf s 1)] else
if not (s.[0] = ' ') && List.mem s.[1] ['(';')';'.';'-'; ']';  '['; ':'; '='; 'E'; 'I'; '&';',' ] then String.concat "" [ssub s 0 1;" "; rectify(suf s 1)]  else
 String.concat "" [ssub s 0 1;rectify (suf s 1)];;

let rec remove list elem = match list with
 a::b -> if a = elem then remove b elem else a::(remove b elem)
  |_ -> list;; 


let rec occ str car = if (String.length str > 0) then if str.[0] = car then true else occ (String.sub str 1 ((String.length str)-1 )) car else false;;

let rec split str car = if (occ str car) = false then [str] else
 let a = (String.index str car) in  [String.sub str 0 a ] @ split (String.sub str (a+1) ((String.length str)-a-1)) car;;

let lexer s = split (rectify (space1 s)) ' ';;


(* end of lexer *)


type sort = BaseSort of string | RelSort of sort list;;

(* must include component for free status (for variable) and position  Variable of string * sort * bool * int |... *)

type term = Variable of string * sort * bool * int | Constant of string * sort * int | I of term * formula * int 
(* | TermBinder of string * term * formula * int
 | TermFunction of string * sort * (term list) * int | Lambda of term * term * int *)
and
formula = E of term * int | App of term * (term list) * int | And of formula * formula * int  | Imp of formula * formula * int | Equiv of term*term * int | Forall of term * formula * int
(* | Predicate of string * int * (term list) * int | FormBinder of string * term * formula * int | FormulaConstant of string * int | BinaryOp of string * formula * formula * int *) ;;

let isTerm t = match t with
 I (a,b,_) -> (match a with
             Variable (c,d,_,_) -> true
             |_ -> false)
 |_ -> true;;


let rec sortEquals (f,g) = match (f,g) with
  (BaseSort a, BaseSort b) -> a = b
 |(RelSort a, RelSort b) -> ( match (a,b) with
                               ([],[]) -> true    
                               |(x::y, z::w) -> sortEquals (x,z) && (sortEquals (RelSort y, RelSort w)) 
                               |(_,_) -> false )                              
 |( _, _) -> false;; 


let rec getSort t = match t with
 Variable (a,b,_,_) -> b
 |Constant (a,b,_) -> b
 | I (a,b,_) -> getSort a;;

let isFormula f = match f with
 Equiv (a,b,_) -> (getSort a) = (getSort b)
 |Forall (x,a,_) -> (match x with
             Variable (c,d,_,_) -> true
             |_ -> false)
 | App (x,y,_) -> let a = getSort x in let b = List.map getSort y in sortEquals (a,RelSort b)
 |_ -> true;;

let varEquals (x,y) = match (x,y) with
 (Variable (a,b,_,_), Variable (c,d,_,_)) -> a = c && sortEquals(b,d)
| _ -> false;;

let rec varMember x l = match l with
 v::w -> if varEquals (x,v) then true else varMember x w
|_-> false;;



let rec freeVarTerm (t,l) = match t with
  I (Variable (a,s,f,p),b,_) -> freeVarForm (b, Variable(a,s,f,p)::l)
  | Variable (x,s,f,p) -> if varMember (Variable (x,s,f,p)) l then l else Variable(x,s,f,p)::l 
  | _ -> l 
and  freeVarForm (f,l) = match f with
  E (a,_) -> freeVarTerm (a,l)
  | Equiv (a,b,_) ->  List.concat [freeVarTerm (a, l); freeVarTerm (b,l)]
  | App (a,c,_) -> let f q = freeVarTerm (q,l) in List.concat ((freeVarTerm(a,l))::(List.map f c))
  | And (a,b,_) -> List.concat [freeVarForm (a, l); freeVarForm (b,l)]
  | Imp (a,b,_) -> List.concat [freeVarForm (a, l); freeVarForm (b,l)]
  | Forall (Variable (a,s,b,p),f,_) -> freeVarForm (f, Variable (a,s,b,p)::l) 
  | _ -> l;;

(*

let rec boundVarTerm (t,l) = match t with
  I (Variable (a,s,f,p),b,_) -> boundVarForm (b, Variable(a,s,f,p)::l)
  | _ -> l
and  boundVarForm (f,l) = match f with
  E (a,_) -> boundVarTerm (a,l)
  | Equiv (a,b,_) ->  List.concat [boundVarTerm (a, l); boundVarTerm (b,l)]
  | App (a,c,_) -> let f q = boundVarTerm (q,l) in List.concat ((boundVarTerm(a,l))::(List.map f c))
  | And (a,b,_) -> List.concat [boundVarForm (a, l); boundVarForm (b,l)]
  | Imp (a,b,_) -> List.concat [boundVarForm (a, l); boundVarForm (b,l)]
  | Forall (Variable (a,s,b,p),f,_) -> boundVarForm (f, Variable (a,s,b,p)::l)
  | _ -> l;;

*)
(* write function to rename bound variables so bound and free variables are disjoint sets *)
(* write function that outputs terms and formulas with correct free status on all variables *)

let rec setFreeTerm (t,l) = match t with
  I (t,b,p) -> I (t, setFreeForm (b, t::l),p)
  | Variable (x,s,f,p) -> if varMember (Variable (x,s,f,p)) l then Variable (x,s,false,p) else Variable(x,s,true,p)
  | Constant(x,s,p) -> Constant (x,s,p)
and  setFreeForm (f,l) = match f with
  E (a,p) -> E (setFreeTerm (a,l), p)
  | Equiv (a,b,p) ->  Equiv (setFreeTerm (a, l), setFreeTerm (b,l), p)
  | App (a,c,p) -> let f q = setFreeTerm (q,l) in App (setFreeTerm(a,l), List.map f c , p)
  | And (a,b,p) -> And (setFreeForm (a, l), setFreeForm (b,l),p)
  | Imp (a,b,p) -> Imp (setFreeForm (a, l), setFreeForm (b,l),p)
  | Forall (t,f,q) -> Forall (t, setFreeForm (f, t::l),q);;



let rec simpleSubTerm (t,s,x) = match t with 
 Variable (a,b,f,p) -> if varEquals( Variable (a,b,f,p), x) && f = true then s else Variable(a,b,f,p)
 | Constant (a,b,p) -> Constant (a,b,p)
 | I (y,f,p) -> if varEquals(x,y) then I(y,f,p) else I(y, simpleSubForm(f,s,x),p)
and simpleSubForm (f,s,x) = match f with
  E (a,p) -> E (simpleSubTerm (a,s,x),p)
  | Equiv (a,b,p) ->  Equiv (simpleSubTerm (a, s,x), simpleSubTerm(b, s,x),p)
  | App (a,c,p) -> let f q = simpleSubTerm (q,s,x) in App (simpleSubTerm (a,s,x), List.map f c , p)
  | And (a,b,p) -> And (simpleSubForm (a , s,x), simpleSubForm (b,s,x),p)
  | Imp (a,b,p) -> Imp(simpleSubForm (a, s,x ), simpleSubForm (b, s, x),p)
  | Forall (Variable (a,w,b,q),f,p) -> if varEquals(Variable(a,w,b,q),x) then Forall (Variable(a,w,b,q),f,p)  else Forall (Variable(a,w,b,q), simpleSubForm( f,s,x),p)
  | _ -> f;;


let rec getBoundTerm t = match t with
  I (t,b,_) -> t::(getBoundForm b)
  | _ -> []
and  getBoundForm f = match f with
  E (a,_) -> getBoundTerm a
  | Equiv (a,b,_) ->  List.concat [getBoundTerm a; getBoundTerm b]
  | App (a,c,_) -> let f q = getBoundTerm q in getBoundTerm a @(List.concat (List.map f c))
  | And (a,b,_) -> List.concat [getBoundForm a; getBoundForm b ]
  | Imp (a,b,_) -> List.concat [getBoundForm a; getBoundForm b]
  | Forall (t,f,_) -> t::(getBoundForm f);;

(* safety all term substitutions must not contain free variables that are in the list of bound variables *)

let rec intersect a b = match a with
 x::y -> if List.mem x b then true else intersect y b
|_ -> false;;


let subTerm t x s = let fs = (getFreeTerm s) in let b = getBoundTerm t in let aux1 = getNames fs in let aux2 = getNames b in 
 if intersect aux1 aux2 then t else simpleSubTerm t x s;;

let subForm t x s = let fs = (getFreeTerm s) in let b = getBoundForm t in let aux1 = getNames fs in let aux2 = getNames b in
 if intersect aux1 aux2 then t else simpleSubForm t x s;;
 

let rec monad list pass n = match list with
 [] -> ([],n)
|a::[] -> ( [fst (pass a n)], snd (pass a n))
|a::b -> let aux = pass a n in let aux2 = monad b pass (snd aux)
in ( (fst aux)::(fst aux2), snd aux2);; 


let rec setPosTerm s n = match s with
  Variable (a,b,f,p) -> (Variable(a,b,f,n), n + 1)
 | Constant (a,b,p) -> (Constant (a,b,n), n + 1)
 | I (y,f,p) ->  let aux = setPosTerm y n in let aux2 = setPosForm f (snd aux) in
 (I( fst aux, fst aux2, snd aux2), snd aux2 + 1)
and setPosForm s n = match s with
  E (a,p) -> let aux = setPosTerm a n in  (E (fst aux, snd aux), snd aux +1)
  | Equiv (a,b,p) ->  let aux = setPosTerm a n in let aux2 = setPosTerm b (snd aux) in 
(Equiv (fst aux, fst aux2, snd aux2), snd aux2 +1)
  | And (a,b,p) ->  let aux = setPosForm a n in let aux2 = setPosForm b (snd aux) in 
(And (fst aux, fst aux2, snd aux2), snd aux2 + 1)
  | Imp (a,b,p) ->  let aux = setPosForm a n in let aux2 = setPosForm b (snd aux) in 
(Imp (fst aux, fst aux2, snd aux2), snd aux2 +1)
  | App (a,c,p) -> let aux = setPosTerm a n in let pass l  m = setPosTerm l m in let aux2 = monad c pass (snd aux) in 
(App (fst aux, fst aux2, snd aux2 ), snd aux2 +1)
  | Forall (y,f,p) ->  let aux = setPosTerm y n in let aux2 = setPosForm f (snd aux) in
 (Forall( fst aux, fst aux2, snd aux2), snd aux2 + 1);;



(* type proof = Proof of formula list;;
let prop1 pr p q = (Imp (p, Imp( q,  p,0), 0 ))::pr ;; *)
     
let vars = ref [];;
let constants = ref[];;
let basesorts = ref[];;

basesorts := [BaseSort "a"];;

let rec getSortNames l = match l with
 (BaseSort a)::b -> a::(getSortNames b)
|_ -> [];; 

vars := [Variable ("x", BaseSort "a", false, 0)] ;;


let rec getPairs l = match l with
 (Variable (a,x,_,_))::b -> (a,x)::getPairs b
 |(Constant (a,x,_))::b -> (a,x)::getPairs b
 |_ -> [];;

let rec getNames l =  match l with
 (Variable (a,x,_,_))::b -> a::getNames b
 |(Constant (a,x,_))::b -> a::getNames b
 |_ -> [];;

(* List.assoc   calculates sorts on the result of getPairs *)

(*parsing *)

let rec binary_op parser1 parser2 ops lex = match lex with
 (a, b::c) -> let v = parser1 (List.rev a) in let w = parser2 c in  if not(v=None) && (List.mem b ops) && not(w = None) then
 Some (v, c, w) else binary_op parser1 parser2 ops (b::a,c)
 |(a, []) -> None;;


let rec prefix l n = match l with
  a::b -> if n > 0 then a:: (prefix b (n-1)) else []
| [] -> [];;

let rec suffix l n = if n = 0 then l else suffix (List.tl l) (n-1);;

let sub l n m = prefix (suffix l n) (m-n);;

let binary_op_wrap parser1 parser2 ops lex =  binary_op parser1 parser2 ops ([], lex);;

let parenthesis_wrap parser lex  = if (List.length lex = 0) then None else if not(List.nth lex 0  = "(") || not(List.nth lex ((List.length lex) -1)  = ")") then None
else parser (sub lex 1 ((List.length lex) - 1 ));;  


let sort_parenthesis_wrap parser lex  = if (List.length lex = 0) then None else if not(List.nth lex 0  = "[") ||  not(List.nth lex ((List.length lex) -1) = "]") then None
else parser (sub lex 1 ((List.length lex) - 1 ));;



let operator_wrap parser op lex  = if (List.length lex = 0) then None else if not(List. mem (List.nth lex 0) op) then None else
 parser (sub lex 1 (List.length lex ));;

 
let rec binary parser1 parser2 lex = match lex with
 (a, b::c) ->  let v = parser1 (List.rev a ) in let w = parser2 (b::c) in if (not(v=None))  && (not(w = None)) then Some (v, w) else binary parser1 parser2 (b::a,c)
 |(a, _) -> None;;

(*let unary s lex = match lex with
 b::[] -> if List.mem b s then Some b else None
|_ -> None;;*)

let binary_wrap parser1 parser2 lex = binary parser1 parser2 ([], lex);;


let rec star parser sep lex = match lex with
 (a,[]) -> if not(parser (List.rev a) = None) then  [parser (List.rev a)] else []
|(a, b::c) ->  if not(parser (List.rev a) = None) && not(star parser sep ([],c) = []) && List.mem b sep then
 [parser (List.rev a)]@(star parser sep ([],c)) else 
star parser sep (b::a,c);;

let star_wrapper parser sep lex = match lex with
 [] -> Some []
|_ -> let aux = star parser sep ([],lex) in if aux = [] then None else Some aux;;

(* actual parser *)

let variable l = match l with
 |a::[] -> let p = getPairs !vars in if List.mem a (getNames !vars) then Some (Variable (a, List.assoc a p, false, 0)) else None
 |_ -> None;;

let constant l = match l with
 |a::[] -> let p = getPairs !constants in if List.mem a (getNames !constants) then Some (Constant (a, List.assoc a p, 0)) else None
 |_ -> None;;

let rec orParse parserlist l = match parserlist with
 p::a -> let v = (p l) in if not (v = None) then v else orParse a l
|[] -> None;;

(*let term l = orParse [variable; constant] l;;*)

let equiv parser l = let v = parenthesis_wrap (binary_op_wrap parser parser ["="]) l in match v with
  Some (a,b,c) ->  (match (a,c) with 
                    (Some x, Some z) -> Some (Equiv (x,z,0))
                    |_ -> None) 
 |_ -> None;;

let conjunction parser l = let v = parenthesis_wrap (binary_op_wrap parser parser ["&"]) l in match v with
  Some (a,b,c) ->  (match (a,c) with
                    (Some x, Some z) -> Some (And (x,z,0))
                    |_ -> None) 
 |_ -> None;;

let implication parser l = let v = parenthesis_wrap (binary_op_wrap parser parser ["->"]) l in match v with
  Some (a,b,c) ->  (match (a,c) with
                    (Some x, Some z) -> Some (Imp (x,z,0))
                    |_ -> None)
 |_ -> None;;

let iota parser1 parser2 l = let v =  operator_wrap (binary_wrap parser1 parser2) ["I"] l in match v with
 Some (Some a, Some b) ->  Some (I (a,b,0))
|_-> None;; 

let forall parser1 parser2 l = let v =  operator_wrap (binary_wrap parser1 parser2 ) ["forall"] l in match v with
 Some (Some a, Some b) ->  Some (Forall (a,b,0))
|_-> None;;

let defined parser l = let v = operator_wrap parser ["E"] l in match v with
 Some a -> Some (E (a,0))
|_ -> None;;

let product parser l = parenthesis_wrap (star_wrapper parser [","]) l;;

let rec extract l = match l with
 (Some a)::b -> a:: extract b
|_ -> [];;

let application parser1 parser2 l = let v = binary_wrap parser1 parser2 l in match v with
  Some (Some a, Some b) -> let w = extract b in Some (App (a,w,0))
 |_ -> None;;


let rec formula l = orParse [ (application term (product term));  (equiv term); (defined term); (conjunction formula); (implication formula); (forall variable formula)] l
 and
 term l = orParse [variable; constant; (iota variable formula)] l;;

let basesort l  = match l with
 |a::[] -> let p = getSortNames !basesorts in if List.mem a p then Some (BaseSort a) else None
 |_ -> None;;

let relsort parser l = let v = sort_parenthesis_wrap(star_wrapper parser [","]) l in match v with
 Some x -> let w = extract x in Some (RelSort w)
|_ -> None;;

let rec sort l = orParse [ basesort ; relsort sort] l;;

(* display expressions *)

let rec printTerm t = match t with
 Variable (a,b,f,p) -> a
 | Constant (a,b,p) -> a
 | I (y,f,p) -> String.concat "" ["I "; printTerm y ; " "; (printFormula f)]
and printFormula f = match f with
  E (a,p) -> String.concat "" ["E "; (printTerm a)]
  | Equiv (a,b,p) -> String.concat "" ["("; printTerm a; " = " ; printTerm b; ")"]
  | App (a,c,p) -> let f q = printTerm q in let aux =  (String.concat "," (List.map f c) ) in 
String.concat "" [printTerm a; "("; aux ; ")"]  
  | And (a,b,p) -> String.concat "" ["("; printFormula a;" & "  ; printFormula b; ")"]
  | Imp (a,b,p) -> String.concat "" ["("; printFormula a;" -> "  ; printFormula b; ")"]
  | Forall (Variable (a,w,b,q),f,p) -> String.concat "" ["forall "; a ;" ";  (printFormula f)]
  | _ -> "";;

let rec printSort s = match s with
 BaseSort a -> a
|RelSort l -> let f x = printSort x in let aux = String.concat ","  (List.map f l) in String.concat "" ["["; aux ; "]"];;

(* add constants, variables and sorts *)

let newBaseSort name = if not (List.mem name (getSortNames !basesorts)) then basesorts:= (BaseSort name)::!basesorts else ();;

let newVariable name s = let aux = sort (lexer s) in if not (List.mem name (getNames !vars))  then match aux with 
 Some f -> vars:= (Variable (name,f, false,0))::!vars
|_ -> ();;

let newConstant name s = let aux = sort (lexer s) in if not (List.mem name (getNames !constants))  then match aux with 
 Some f -> vars:= (Constant (name,f,0))::!constants  
|_ -> ();;


