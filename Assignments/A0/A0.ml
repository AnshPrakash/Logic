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
Hashtbl.add rho "h" true;;
Hashtbl.add rho "Aux" true;;

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


let rec cnff p = match p with
				| T -> T
				| F -> F
				| Not(q) -> p
				| And(q1,q2) -> And(cnff q1, cnff q2)
				| Or(And(q1,w),q2) -> cnff (nnf (And(Impl(L("Aux"),And(q1,w)),Impl(Not(L("Aux")),q2))))  (* convert it to nnf again*)
				| Or(q1,And(q2,w)) -> cnff (nnf (And(Impl(L("Aux"),q1),Impl(Not(L("Aux")),And(q2,w)))))
				| Or(Or(q1,w),q2) -> cnff (Or(cnff (Or(q1,w)) ,q2))
				| Or(q1,Or(q2,w)) -> cnff (Or(q1,cnff (Or(q2,w)) ))
				| Or(q1,q2) -> p
				| L(s) -> p

;;

(* Wrapper function required *)
let cnf p =  cnff (nnf p);;

let rec dnff p= match p with
				| T -> T
				| F -> F
				| Not(q) -> p
				| Or(q1,q2) -> Or(dnff q1, dnff q2)
				| And(Or(q1,w),q2) ->
				| And(q1,Or(q2,w)) ->
				| And(And(q1,w),q2) ->
				| And(q1,And(q2,w)) ->
				| And(q1,q2) -> p
				| L(s) -> p

;;


let dnf p = dnff (nnf p);;


let rec subprop_at p1 p2 = ();;

(* TestCases *)

print_int (ht (And(T,And(T,T))));;
print_string ("\n");;

let s = letters (Or(And(L("A"),T),Impl(L("B"),L("A")))) SS.empty;;
print_set s;;