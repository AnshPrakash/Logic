module SS = Set.Make(String);;

type prop = T | F | L of string | Not of prop | And of prop*prop 
			| Or  of prop*prop | Impl of prop*prop | Iff of prop*prop
;;

(* Printing sets *)
let print_set s =  SS.iter print_endline s;;


let rec ht p = match p with
				| T -> 0 
				| F -> 0
				| Not(q) -> 1 + (ht q)
				| And(q1,q2) -> 1 + (max (ht q1) (ht q2)) 
				| Or(q1,q2) -> 1 + (max (ht q1) (ht q2)) 
				| Impl(q1,q2) -> 1 + (max (ht q1) (ht q2)) 
				| Iff(q1,q2) -> 1 + (max (ht q1) (ht q2))
				| L(s) -> 0
;;


let rec size p = match p with
				| T -> 1 
				| F -> 1
				| Not(q) -> 1 + (size q)
				| And(q1,q2) -> 1 +  (size q1) + (size q2)
				| Or(q1,q2) -> 1 + (size q1) + (size q2) 
				| Impl(q1,q2) -> 1 + (size q1) + (size q2)
				| Iff(q1,q2) -> 1 + (size q1) + (size q2)
				| L(s) -> 1
;;				


let rec letters p s= match p with
					| T -> s
					| F -> s
					| Not(q) -> letters q s
					| And(q1,q2) -> SS.union (letters q1 s) (letters q2 s)
					| Or(q1,q2) -> SS.union (letters q1 s) (letters q2 s)
					| Impl(q1,q2) -> SS.union (letters q1 s) (letters q2 s)
					| Iff(q1,q2) -> SS.union (letters q1 s) (letters q2 s)
					| L(st) -> SS.add st s
;;

let rho = Hashtbl.create 1234;; (*HashTable*)
Hashtbl.add rho "A" false;;
Hashtbl.add rho "B" true;;

let rec truth p rho = match p with
					| T -> true
					| F -> false
					| Not(q) -> not (truth q rho)
					| And(q1,q2) -> (truth q1 rho) && (truth q2 rho)
					| Or(q1,q2) -> (truth q1 rho) || (truth q2 rho)
					| Impl(q1,q2) -> (not (truth q1 rho)) || (truth q2 rho)
					| Iff(q1,q2) -> (truth (Impl(q1,q2)) rho) && ((truth (Impl(q2,q1)) rho))
					| L(st) -> Hashtbl.find rho st
;;


let rec nnf p = match p with
				| T -> T
				| F -> F
				| Not(T) -> F
				| Not(F) -> T
				| Not(Not(q)) -> nnf q
				| Not(L(s)) -> p
				| Not(Impl(q1,q2)) -> nnf (And(Not(q2),q1))
				| Not(Iff(q1,q2)) -> nnf (Not(And(Impl(q1,q2),Impl(q2,q1))))
				| Impl(q1,q2) -> Or(nnf (Not(q1)),nnf q2)
				| Iff(q1,q2) ->  And( nnf (Impl(q1,q2)), nnf (Impl(q2,q1)) )
				| Not(And(q1,q2)) -> Or(nnf (Not(q1)), nnf (Not(q2)))
				| Not(Or(q1,q2)) -> And(nnf (Not(q1)), nnf (Not(q2)))
				| And(q1,q2) -> And(nnf q1, nnf q2)
				| Or(q1,q2) -> Or(nnf q1, nnf q2)
				| L(st) -> p
;;


let rec subAnd p  = match p with
				| T -> false
				| F -> false
				| Not(q) -> false
				| And(q1,q2) -> true
				| Or(q1,q2) -> (subAnd q1) || (subAnd q2)
				| L(st) -> false
;;

let rec subOr p  = match p with
				| T -> false
				| F -> false
				| Not(q) -> false
				| Or(q1,q2) -> true
				| And(q1,q2) -> (subOr q1) || (subOr q2)
				| L(st) -> false
;;

let rec cnff p = match p with
				| T -> T
				| F -> F
				| Not(q) -> p
				| And(q1,q2) -> And(cnff q1, cnff q2)
				| Or(And(q1,w),q2) -> cnff (And(Or(q2,w),Or(q2,q1)))
				| Or(q1,And(q2,w)) -> cnff (And(Or(q1,w),Or(q2,q1)))
				| Or(q1,q2) ->  if (subAnd q1) then cnff (Or ( cnff q1, q2) )
								else if (subAnd q2) then cnff (Or ( q1, cnff q2) )
								else p
				| L(s) -> p

;;

(* Wrapper function required *)
let cnf p =  cnff (nnf p);;

let rec dnff p= match p with
				| T -> T
				| F -> F
				| Not(q) -> p
				| Or(q1,q2) -> Or(dnff q1, dnff q2)
				| And(Or(q1,w),q2) -> dnff ( Or(And(q2,w),And(q2,q1)) )
				| And(q1,Or(q2,w)) -> dnff ( Or(And(q1,w),And(q2,q1)) )
				| And(q1,q2) -> if (subOr q1) then dnff (And ( dnff q1, q2) )
								else if (subOr q2) then dnff (And ( q1, dnff q2) )
								else p
				| L(s) -> p
;;


let dnf p = dnff (nnf p);;

let rec isSame p1 p2 = match p1,p2 with
					| T,T -> true
					| F,F -> true
					| Not(q1),Not(q2) -> isSame q1 q2
					| And(q1,q2),And(q3,q4) -> (isSame q1 q3) && (isSame q2 q4)
					| Or(q1,q2),Or(q3,q4) -> (isSame q1 q3) && (isSame q2 q4)
					| Impl(q1,q2),Impl(q3,q4) -> (isSame q1 q3) && (isSame q2 q4)
					| Iff(q1,q2),Iff(q3,q4) -> (isSame q1 q3) && (isSame q2 q4)
					| L(s1),L(s2) ->  (s1=s2)
					| _-> false
;;

(* p1 is subpropostion *)

(* when there is only one path then bit is 0(Not(p)) *)

let rec subprop p1 p2 s str =	if (isSame p1 p2) then SS.add str s
								else match p2 with
								| T           -> s
								| F           -> s
								| Not(q)      -> subprop p1 q s (str^"0")
								| And(q1,q2)  -> SS.union (SS.union (subprop p1 q1 s (str^"0") ) (subprop p1 q2 s (str^"1"))) s
								| Or(q1,q2)   -> SS.union (SS.union (subprop p1 q1 s (str^"0") ) (subprop p1 q2 s (str^"1"))) s
								| Impl(q1,q2) -> SS.union (SS.union (subprop p1 q1 s (str^"0") ) (subprop p1 q2 s (str^"1"))) s
								| Iff(q1,q2)  -> SS.union (SS.union (subprop p1 q1 s (str^"0") ) (subprop p1 q2 s (str^"1"))) s
								| L(st)       -> s

;;
let subprop_at p1 p2 = subprop p1 p2 SS.empty "";;

(* TestCases *)

print_int (ht (And(T,And(T,T))));;
print_string ("\n");;

let s = letters (Or(And(L("A"),T),Impl(L("B"),L("A")))) SS.empty;;
print_set s;;

print_set (subprop_at (Or(And(L("A"),T),Impl(L("B"),L("A")))) (Or(And(L("A"),T),Impl(L("B"),L("A")))))
;;
print_set (subprop_at (Impl(L("B"),L("A"))) (Or(And(L("A"),Impl(L("B"),L("A"))),Impl(L("B"),L("A")))))
;;


let a = cnf (Or(And(L("A"),T),Impl(L("B"),L("A"))));;
let b = dnf (Or(And(L("A"),T),Impl(L("B"),L("A"))));;
let c = nnf (Or(And(L("A"),T),Impl(L("B"),L("A"))));;

truth a rho;;
truth b rho;;
truth c rho;;
truth (Or(And(L("A"),T),Impl(L("B"),L("A")))) rho;;

