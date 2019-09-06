(* Hilbert Style Proof *)

type prop = T | F | L of string | Not of prop | And of prop*prop 
			| Or  of prop*prop | Impl of prop*prop | Iff of prop*prop
;;

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

exception Not_Found of string;;
exception Contrad ;;
exception Not_Valid ;;


type assumptions = Assum of prop list;;
type entails = Entails of assumptions* prop;; 
type hprooftree =  Base of entails | MP of hprooftree* hprooftree* entails;;

let check_axiom_k axiom = 
	match axiom with
	(* K *)
	| Impl(p,Impl(q,r)) -> (isSame p r)
	| _ -> false
;;
let check_axiom_r axiom =
	match axiom with
	(* R *)
	| Impl(Impl(Not(p),Not(q)),Impl(Impl(Not(p1),q1),p2))-> (
			if (isSame p p1) && (isSame p p2) && (isSame q q1) then true
			else false
		)
	| _ ->false
;;
let check_axiom_s axiom =
	match axiom with
	(* S *)
	| Impl(Impl(p,Impl(q,r)),Impl(Impl(p1,q1),Impl(p2,r1))) -> (
			if (isSame p p1) && (isSame p p2) && (isSame q q1) && (isSame r r1) then true
			else false
		)
	| _ -> false
;;

let check_axiom axiom =  (check_axiom_r axiom) || (check_axiom_s axiom) || (check_axiom_k axiom)
;;
	
let rec check_assumption assumptions p =
	match assumptions with
	| Assum([]) -> false
	| Assum(hd::tl) -> (isSame p hd) || check_assumption (Assum(tl)) p
;;

let get_entails htree =
	match htree with
	| Base(e) -> e
	| MP(ht1,ht2,e) -> e
;;


let split_impl p = 
	match p with
	| Impl(p1,p2) -> (p1,p2)
	| _ -> raise Not_Valid
;;


let rec is_element p ass = 
	match ass with
	| Assum([]) -> false
	| Assum(hd::tl) -> (isSame hd p) || is_element p (Assum(tl))
;;

(* check if g1 is subset of g2 *)
let rec assumption_subset g1 g2 = 
	match g1 with
	| Assum([]) -> true
	| Assum(hd::tl) -> (is_element hd g2) && assumption_subset (Assum(tl)) g2
;;


let isEqualAssum g1 g2 = (assumption_subset g1 g2) && (assumption_subset g2 g1);;


let rec valid_hprooftree proof = 
	match proof with
	| Base(Entails(Assum(l),p)) -> (check_axiom p) || check_assumption (Assum(l)) p
	| MP(hp1,hp2,Entails(Assum(l),p)) -> (
			let e1,e2 = (get_entails hp1),(get_entails hp2) in (
				match e1,e2 with
				| (Entails(assu1,p1),Entails(assu2,p2))-> (
						if 	(isEqualAssum assu1 assu2) && (isEqualAssum assu1 (Assum(l))) then (
							try (
									let (p1_1,p1_2) = split_impl p1 in (
									(isSame p1_1 p2) && (isSame p1_2 p) && (valid_hprooftree hp1) && (valid_hprooftree hp2)
								)
							)
							with Not_Valid -> false
						)
						else false
					)
			)
		)
;;


let rec pad proof props =
	match proof with
	| Base(Entails(Assum(l),p)) -> Base(Entails(Assum(l@props),p))
	| MP(hp1,hp2,Entails(Assum(l),p)) -> MP(pad hp1 props,pad hp2 props,Entails(Assum(l@props),p))
;;

let rec getbases hptree  = 
	match hptree with
		| Base(Entails(Assum(l),p)) -> if (check_assumption (Assum(l)) p)  then p::[] else []
		| MP(hp1,hp2,Entails(Assum(l),p)) -> (getbases hp1)@(getbases hp2)
;;

let setify gamma = 
	let rec stif proplist setified = 
		(	match proplist with
			| [] -> setified
			| hd::tl ->  if (is_element hd (Assum(tl))) then (stif tl (hd::setified)) else (stif tl setified)
		) in
		(stif gamma ([]))
;;

let rec prune prooft = 
	let subprops = setify (getbases prooft) in 
	let rec replace hproof newprops =
	(	match hproof with
		| Base(Entails(Assum(l),p)) -> Base(Entails(Assum(newprops),p))
		| MP(hp1,hp2,Entails(Assum(l),p)) -> MP(replace hp1 newprops,replace hp2 newprops,Entails(Assum(newprops),p))
	) in (replace prooft subprops)
;;


let getassum hptree = 
	match hptree with
	| Base(Entails(assum,p)) -> assum
	| MP(hp1,hp2,Entails(assum,p)) -> assum
;;


let getpos lis q=
	let rec position l i =
		(	match l with
			| [] -> raise (Not_Found("not in list"))
			| hd::tl -> if (isSame q hd) then (i) else position tl (i+1)
		) in (position lis 0)
;;

let rec get_ith_element lis i = 
	match lis with
	| [] -> raise Not_Valid
	| hd::tl -> if i = 0 then hd else get_ith_element tl (i-1)
;;

let rec graft proof prooflist = 
	let newgamma = 
	(	match prooflist with
		| [] -> Assum([])
		| hd::tl -> getassum hd
	) in (
	let rec subs htree =
	(
		match htree with
		| Base(Entails(Assum(l),p)) -> 
		(	try (
				let pos = getpos l p  in (get_ith_element prooflist pos )
			)
			with Not_Found(e) -> htree
		)
		| MP(hp1,hp2,e) -> MP(subs hp1 ,subs hp2 ,e)
	) in let partial_pf = subs proof in (
		let rec replace_gamma pf gamma_pri = (
			match pf with
			| Base(Entails(assum,p)) -> Base(Entails(gamma_pri,p))
			| MP(hp1,hp2,Entails(assum,p)) -> MP(replace_gamma hp1 gamma_pri,replace_gamma hp2 gamma_pri,Entails(gamma_pri,p))
			) in ( replace_gamma partial_pf newgamma)
		)
	)

;;

(* let rec dedthm proof =;; *)


(* let p = Node( Node(Impl(p,q))|Base(), Node(q), MP(Ifthen(Assum([]),p,q,r))) *)


let p = Base((Entails(Assum([]),Impl(L("p"),L("p")))));;

let p = MP(Ifthen(Assum([]),Impl(Impl(L("p"),Impl(L("p"),L("p"))),Impl(L("p"),L("p")) ), Impl(L("p"),Impl(L("p"),L("p")))), 
							Entails(Assum([]),Impl(Impl(L("p"),Impl(L("p"),L("p"))),Impl(L("p"),L("p")) )),
									Entails(Assum([]),Impl(L("p"),L("p"))))

Entails(Assum([]),Impl(Impl(L("p"),Impl(L("p"),L("p"))),Impl(L("p"),L("p")) ))
  Entails(Assum([]),Impl(L("p"),L("p")))