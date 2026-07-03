
(*lexer*)

let ssub s n m = String.sub s n (m-n);;
let suf s n = let l = String.length s in ssub s n l;;

let rec space1 s = if String.length s < 2 then s else if (ssub s 0 2) = "  " then space1 (suf s 1) else
String.concat "" [ssub s 0 1; space1 (suf s 1)] ;;


let rec spaceremove s = if s = "" then s else if s.[0] = ' ' then spaceremove (suf s 1) else String.concat "" [ssub s 0 1; spaceremove (suf s 1)];;

let rec rectify s = if String.length s < 2 then s else if List.mem s.[0] ['(';')';'.';'>';']'; '['; ':'; '='; 'E'; 'I'; '&'; ','; 'V'] && not (s.[1]=' ') then
String.concat "" [ssub s 0 1;" ";rectify (suf s 1)] else
if not (s.[0] = ' ') && List.mem s.[1] ['(';')';'.'; ']';  '['; ':'; '='; 'E'; 'I'; '&';','; 'V'  ] then String.concat "" [ssub s 0 1;" "; rectify(suf s 1)]  else
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
formula = E of term * int | App of term * (term list) * int | BinaryOp of string * formula * formula * int  | UnaryOp of string * formula * int | Equiv of term*term * int |
 Binder of string * term * formula * int | PropConstant of string * int;;
 
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
 |Binder (n,x,a,_) -> (match x with
             Variable (c,d,_,_) -> true
             |_ -> false)
 | App (x,y,_) -> let a = getSort x in let b = List.map getSort y in sortEquals (a,RelSort b)
 |_ -> true;;

let varEquals (x,y) = match (x,y) with
 (Variable (a,b,_,_), Variable (c,d,_,_)) -> a = c && sortEquals(b,d)
| _ -> false;;

let conEquals (x,y) = match (x,y) with
 (Constant (a,b,_), Constant (c,d,_)) -> a = c && sortEquals(b,d)
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
  | BinaryOp (n,a,b,_) -> List.concat [freeVarForm (a, l); freeVarForm (b,l)]
  | UnaryOp (n,a,_) -> freeVarForm (a, l)
  | Binder(n,Variable (a,s,b,p),f,_) -> freeVarForm (f, Variable (a,s,b,p)::l) 
  | _ -> l;;

(* write function that outputs terms and formulas with correct free status on all variables *)

let rec setFreeTerm (t,l) = match t with
  I (t,b,p) -> I (t, setFreeForm (b, t::l),p)
  | Variable (x,s,f,p) -> if varMember (Variable (x,s,f,p)) l then Variable (x,s,false,p) else Variable(x,s,true,p)
  | Constant(x,s,p) -> Constant (x,s,p)
and  setFreeForm (f,l) = match f with
  E (a,p) -> E (setFreeTerm (a,l), p)
  | Equiv (a,b,p) ->  Equiv (setFreeTerm (a, l), setFreeTerm (b,l), p)
  | App (a,c,p) -> let f q = setFreeTerm (q,l) in App (setFreeTerm(a,l), List.map f c , p)
  | BinaryOp (n,a,b,p) -> BinaryOp (n,setFreeForm (a, l), setFreeForm (b,l),p)
  | UnaryOp (n,a,p) -> UnaryOp (n, setFreeForm (a, l),p)
  | Binder (n,t,f,q) -> Binder (n,t, setFreeForm (f, t::l),q)
  | PropConstant (n,p)-> PropConstant (n,p);;

let setFreeTerm_wrap t = setFreeTerm(t,[]);;
let setFreeForm_wrap f = setFreeForm(f,[]);;

(* must check that sort of s and x are the same *)
let rec simpleSubTerm (t,s,x) = match t with 
 Variable (a,b,f,p) -> if varEquals( Variable (a,b,f,p), x) && f = true then s else Variable(a,b,f,p)
 | Constant (a,b,p) -> Constant (a,b,p)
 | I (y,f,p) -> if varEquals(x,y) then I(y,f,p) else I(y, simpleSubForm(f,s,x),p)
and simpleSubForm (f,s,x) = match f with
  E (a,p) -> E (simpleSubTerm (a,s,x),p)
  | Equiv (a,b,p) ->  Equiv (simpleSubTerm (a, s,x), simpleSubTerm(b, s,x),p)
  | App (a,c,p) -> let f q = simpleSubTerm (q,s,x) in App (simpleSubTerm (a,s,x), List.map f c , p)
  | BinaryOp (n,a,b,p) -> BinaryOp (n,simpleSubForm (a , s,x), simpleSubForm (b,s,x),p)
  | UnaryOp (n,a,p) -> UnaryOp(n, simpleSubForm (a, s,x ),p)
  | Binder (n,Variable (a,w,b,q),f,p) -> if varEquals(Variable(a,w,b,q),x) then Binder (n,Variable(a,w,b,q),f,p)  else Binder (n, Variable(a,w,b,q), simpleSubForm( f,s,x),p)
  | _ -> f;;


let rec getBoundTerm t = match t with
  I (t,b,_) -> t::(getBoundForm b)
  | _ -> []
and  getBoundForm f = match f with
  E (a,_) -> getBoundTerm a
  | Equiv (a,b,_) ->  List.concat [getBoundTerm a; getBoundTerm b]
  | App (a,c,_) -> let f q = getBoundTerm q in getBoundTerm a @(List.concat (List.map f c))
  | BinaryOp (n,a,b,_) -> List.concat [getBoundForm a; getBoundForm b ]
  | UnaryOp (n,a,_) -> getBoundForm a
  | Binder (n,t,f,_) -> t::(getBoundForm f)
  | PropConstant (n,p) -> [];;

(* safety all term substitutions must not contain free variables that are in the list of bound variables *)

let rec intersect a b = match a with
 x::y -> if List.mem x b then true else intersect y b
|_ -> false;;

 

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
  | BinaryOp (m,a,b,p) ->  let aux = setPosForm a n in let aux2 = setPosForm b (snd aux) in 
(BinaryOp (m,fst aux, fst aux2, snd aux2), snd aux2 + 1)
  | UnaryOp (m,a,p) ->  let aux = setPosForm a n in  (UnaryOp (m, fst aux, snd aux), snd aux +1)
  | App (a,c,p) -> let aux = setPosTerm a n in let pass l  m = setPosTerm l m in let aux2 = monad c pass (snd aux) in 
(App (fst aux, fst aux2, snd aux2 ), snd aux2 +1)
  | Binder (m,y,f,p) ->  let aux = setPosTerm y n in let aux2 = setPosForm f (snd aux) in
 (Binder(m, fst aux, fst aux2, snd aux2), snd aux2 + 1)
 |PropConstant (m,p) -> (PropConstant (m,n), n+1) ;;

     
let vars = ref [];;
let constants = ref[];;
let basesorts = ref[];;
let propconstants = ref[];;

basesorts := [BaseSort "a"];;

propconstants := [PropConstant ("T", 0); PropConstant("F",0) ] ;;

let rec getSortNames l = match l with
 (BaseSort a)::b -> a::(getSortNames b)
|_ -> [];; 

let rec getPropNames l = match l with
 (PropConstant(a,_))::b -> a::(getPropNames b)
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


let check_subTerm t s   = let fs = (freeVarTerm (s,[])) in let b = getBoundTerm t in let aux1 = getNames fs in let aux2 = getNames b in
 if intersect aux1 aux2 then false else true;;

let check_subForm t s = let fs = (freeVarTerm (s,[])) in let b = getBoundForm t in let aux1 = getNames fs in let aux2 = getNames b in
 if intersect aux1 aux2 then false else true;;                 


let subTerm t  s x = let fs = (freeVarTerm (s,[])) in let b = getBoundTerm t in let aux1 = getNames fs in let aux2 = getNames b in
 if intersect aux1 aux2 then t else simpleSubTerm (t,s,x);;

let subForm t  s x = let fs = (freeVarTerm (s,[])) in let b = getBoundForm t in let aux1 = getNames fs in let aux2 = getNames b in
 if intersect aux1 aux2 then t else simpleSubForm (t,s,x);; 


(* List.assoc   calculates sorts on the result of getPairs *)

(*parsing *)

let rec binary_op parser1 parser2 ops lex = match lex with
 (a, b::c) -> let v = parser1 (List.rev a) in let w = parser2 c in  if not(v=None) && (List.mem b ops) && not(w = None) then
 Some (v, b, w) else binary_op parser1 parser2 ops (b::a,c)
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

let propconstant l = match l with
|a::[] -> if List.mem a (getPropNames !propconstants) then Some (PropConstant (a,0)) else None
|_ -> None;;

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

let binaryop parser l = let v = parenthesis_wrap (binary_op_wrap parser parser ["&"; "->";"V";"<->"]) l in match v with
  Some (a,b,c) -> (match (a,c) with
                    (Some x, Some z) -> Some (BinaryOp (b,x,z,0))
                    |_ -> None) 
 |_ -> None;;

(*let implication parser l = let v = parenthesis_wrap (binary_op_wrap parser parser ["->"]) l in match v with
  Some (a,b,c) ->  (match (a,c) with
                    (Some x, Some z) -> Some (Imp (x,z,0))
                    |_ -> None)
 |_ -> None;;*)

let iota parser1 parser2 l = let v =  operator_wrap (binary_wrap parser1 parser2) ["I"] l in match v with
 Some (Some a, Some b) ->  Some (I (a,b,0))
|_-> None;; 

let forall parser1 parser2 l = let v =  operator_wrap (binary_wrap parser1 parser2 ) ["forall"] l in match v with
 Some (Some a, Some b) ->  Some (Binder ("forll", a,b,0))
|_-> None;;

let exists parser1 parser2 l = let v =  operator_wrap (binary_wrap parser1 parser2 ) ["exists"] l in match v with
 Some (Some a, Some b) ->  Some (Binder ("exists", a,b,0))
|_-> None;;


let negation parser l = let v = operator_wrap parser ["not"] l in match v with
 Some a -> Some (UnaryOp ("negation", a,0))
|_ -> None;;

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


let rec formula l = orParse [ (application term (product term));  (equiv term); (defined term); (negation formula);(binaryop formula); (exists variable formula) ; 
(forall variable formula); propconstant] l
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
  | BinaryOp (n,a,b,p) -> String.concat "" ["("; printFormula a; " ";n;" ";   printFormula b; ")"]
  | UnaryOp (n,a,p) -> String.concat "" [n; "("; printFormula a; ")"]
  | Binder (n, Variable (a,w,b,q),f,p) -> String.concat "" [n ;" "; a ;" ";  (printFormula f)]
  |PropConstant (n,p) -> n
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
 Some f -> constants:= (Constant (name,f,0))::!constants  
|_ -> ();;


let displayTerm x = match x with
                    |Some a -> printTerm a
                    |_ -> "";;

let displayFormula x = match x with
                    |Some a -> printFormula a
                    |_ -> "";;

(*equality of formulas and terms must involve renaming bound variables *)


let rec boolList f l1 l2 = if not(List.length l1 = List.length l2) then false else match l1 with
 a::b -> (match l2 with
            c::d -> (f a c) && boolList f b d
           |_-> false)
|[] -> (match l2 with
            [] -> true
           |_ -> false);;



let rec termEquality t1 t2 k = match t1 with

 Constant (n,s,p) -> (match t2 with 
                        Constant (m,t,q) -> conEquals (Constant(n,s,p), Constant(m,t,q))
                       |_ -> false)
|Variable (n,s,f,p) -> (match t2 with
                       Variable (m, h,o, q) -> varEquals(Variable(n,s,f,p), Variable(m,h,o,q)) 
                       |_-> false)
| I (v1, a, e)  -> (match t2 with
                     I (v2,b, q) -> let aux1 = setFreeForm_wrap a in let aux2 = setFreeForm_wrap b in 
 let aux3 = simpleSubForm (aux1, v1, (Variable(Int.to_string(k), getSort v1, false,0))) in let aux4 = simpleSubForm (aux2, v2, (Variable(Int.to_string(k), getSort v2, false,0))) in
 formulaEquality aux3 aux4 (k+1)
                     |_ -> false)
and formulaEquality f1 f2 k = match f1 with
 PropConstant (a,p) -> (match f2 with
                     PropConstant (b,q) -> a = b
                    |_ -> false)
| BinaryOp (n,a,b,p) -> (match f2 with
                        BinaryOp(m,c,d,q) -> m = n && formulaEquality a c k && formulaEquality b d k
                       |_ -> false)
| UnaryOp(n,a,p) -> (match f2 with
                       UnaryOp(m,b,_) -> m = n && formulaEquality a b k
                      |_ -> false)
| Equiv (a,b,_) -> (match f2 with
                       Equiv (c,d,p) -> termEquality a c k && termEquality b d k
                      |_ -> false)
| Binder (n,v1, a, p) -> (match f2 with
                      Binder(m,v2,b,q) -> n = m &&  let aux1 = setFreeForm_wrap a in let aux2 = setFreeForm_wrap b in
 let aux3 = simpleSubForm (aux1,v1,(Variable(Int.to_string(k),getSort v1, false,0))) in let aux4 = simpleSubForm (aux2,v2,(Variable(Int.to_string(k),getSort v2, false,0))) in
 formulaEquality aux3 aux4 (k+1)
                    |_ -> false)
| E (t,p) -> (match f2 with 
                     E(s,q) -> termEquality t s k
                    |_ -> false)
| App (t, l, p ) -> (match f2 with
                   App (s, m, q) ->  termEquality t s k && let f x y = termEquality x y k in boolList f l m 
                  |_ -> false)   ;;

let termEquality_wrap t1 t2 = termEquality t1 t2 0;;
let formulaEquality_wrap t1 t2 = formulaEquality t1 t2 0;;

