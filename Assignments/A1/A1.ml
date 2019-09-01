module SS = Set.Make(String);;


type prop = T | F | L of string | Not of prop | And of prop*prop 
			| Or  of prop*prop | Impl of prop*prop | Iff of prop*prop
;;


exception Not_Found of string;;
exception Contrad;;

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



(*  -1:contradiction ,   0 :unexamined,  1: examined,   2:selected *)
type status =  {mutable value:int}
;;

type node = Node of prop*bool*status
;;

type tree = Leaf of node| Alpha of node*tree | Beta of node*tree*tree
;;

type example = L of ((string*bool) list)
;;

type proof = P of tree | E of example
;;


let rho = Hashtbl.create 1234;; (*HashTable*)
Hashtbl.add rho "A" false;;
Hashtbl.add rho "B" true;;

(* hellper for contrad_path *)
let update n rho = 	match n with
					| Node(p,b,s) -> match p with
									| L(st) ->(	try (if (Hashtbl.find rho st) != b then (s.value <- -1;raise Contrad) else rho)
												with Not_found -> let rho1 = Hashtbl.copy rho in (Hashtbl.add rho1 st b;rho1) )
									| _ ->  rho
;;

let setbase n = match n with
					| Node(p,b,s)-> if (p = T && b = false) then (s.value <- -1;true)
									else if p = F && b = true then (s.value <- -1 ; true)
									else if p = T || p = F then (false)
									else false
;;

(* let rec contrad_path t rho = match t with 
							| Leaf(n) ->(	try (let _ = update n rho in (setbase n))
											with Contrad -> true
										)
							| Alpha(n,t1) ->(	try (let rho1 = update n rho in contrad_path t1 rho1)
												with Contrad -> true
											) 
							| Beta(n,t1,t2)	->	(	try (let rho1 = update n rho in (contrad_path t1 rho1) || (contrad_path t2 rho1))
													with Contrad -> true
												) 

;;
 *)

let rec contrad_path t rho = match t with 
							| Leaf(n) ->(	try (let _ = update n rho in ((setbase n);t))
											with Contrad -> t
										)
							| Alpha(n,t1) ->(	try (let rho1 = update n rho in Alpha(n,contrad_path t1 rho1))
												with Contrad -> t
											) 
							| Beta(n,t1,t2)	->	(	try (let rho1 = update n rho in Beta(n,contrad_path t1 rho1,contrad_path t2 rho1) )
													with Contrad -> t
												) 

;;

(* 
let rec select_node t = match t with
						| Leaf(Node(p,b,s)) -> if (s.value = 0) then (s.value <- 2; true) else false
						| Alpha(Node(p,b,s),t1) ->  if (s.value = 0) then (s.value <- 2; true) else select_node t1
						| Beta(Node(p,b,s),t1,t2) ->	if (s.value = 0) then (s.value <- 2; true) 
														else if (select_node t1) then true 
														else (select_node t2)
;; *)

let rec select_node t = match t with
						| Leaf(Node(p,b,s)) -> if (s.value = 0) then (s.value <- 2; (true,t)) else (false,t)
						| Alpha(Node(p,b,s),t1) ->  if (s.value = 0) then (s.value <- 2; (true,t)) 
													else let (tb,tt1) = (select_node t1) in
															(tb,Alpha(Node(p,b,s),tt1))
																
						| Beta(Node(p,b,s),t1,t2) ->	if (s.value = 0) then (s.value <- 2; (true,t) )
														else let (tb1,tt1) = select_node t1 in
																if tb1 then (true,Beta(Node(p,b,s),tt1,t2))
																else let (tb2,tt2) = select_node t2 in
																		(tb2,Beta(Node(p,b,s),t1,tt2))
														
;;


let expand t = match t with
	| Leaf(Node(p,b,s)) -> 	( s.value <- 1;
								match (p,b) with
								(* Alpha nodes *)
								| (And(q1,q2),true)-> Alpha(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Leaf(Node(q2,true,{value=0}))))
								| (Or(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,false,{value=0}),Leaf(Node(q2,false,{value=0}))))
								| (Impl(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Leaf(Node(q2,false,{value=0}))))
								(* Beta nodes *)
								| (And(q1,q2),false)-> Beta(Node(p,b,s),Leaf(Node(q1,false,{value = 0})),Leaf(Node(q2,false,{value=0})))
								| (Or(q1,q2),true) -> Beta(Node(p,b,s),Leaf(Node(q1,true,{value = 0})),Leaf(Node(q2,true,{value=0})))
								| (Impl(q1,q2),true) -> Beta(Node(p,b,s),Leaf(Node(q1,false,{value = 0})),Leaf(Node(q2,true,{value=0})))
								(* Iff node *)
								| (Iff(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Leaf(Node(q2,true,{value=0})))
															, Alpha(Node(q1,false,{value=0}),Leaf(Node(q2,false,{value=0})))
															)
								| (Iff(q1,q2),false) -> Beta(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Leaf(Node(q2,false,{value=0})))
															, Alpha(Node(q1,false,{value=0}),Leaf(Node(q2,true,{value=0})))
															)
								(* Leaf Nodes *)
								| (L(st),_) -> t
								| (Not(q),_) -> Leaf(Node(q, not b,{value =0}))
								| (T,true) -> t
								| (F,false) -> t
							)
	| Alpha(Node(p,b,s),t1) -> ( s.value <- 1;
								match (p,b) with
								(* Alpha nodes *)
								| (And(q1,q2),true)-> Alpha(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Alpha(Node(q2,true,{value =0}),t1)))
								| (Or(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,false,{value=0}),Alpha(Node(q2,false,{value =0}),t1)))
								| (Impl(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Alpha(Node(q2,false,{value =0}),t1)))
								(* Beta nodes *)
								| (And(q1,q2),false)-> Beta(Node(p,b,s),Alpha(Node(q1,false,{value=0}),t1),Alpha(Node(q2,false,{value=0}),t1))
								| (Or(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,true,{value=0}),t1),Alpha(Node(q2,true,{value=0}),t1))
								| (Impl(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,false,{value=0}),t1),Alpha(Node(q2,true,{value=0}),t1))
								(* Iff node *)
								| (Iff(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Alpha(Node(q2,true,{value=0}),t1)),Alpha(Node(q1,false,{value=0}),Alpha(Node(q2,false,{value=0}),t1)))
								| (Iff(q1,q2),false) -> Beta(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Alpha(Node(q2,false,{value=0}),t1)),Alpha(Node(q1,false,{value=0}),Alpha(Node(q2,true,{value=0}),t1)))
								(* Leaf Nodes *)
								| (L(st),_) -> t
								| (Not(q),_) -> Alpha(Node(q,not b,{value=0}),t1)
								| (T,true) -> t
								| (F,false) -> t
							)
	| Beta(Node(p,b,s),t1,t2) -> ( s.value <- 1;
								match (p,b) with
								(* Alpha nodes *)
								| (And(q1,q2),true)-> Alpha(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Beta(Node(q2,true,{value=0}),t1,t2)))
								| (Or(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,false,{value=0}),Beta(Node(q2,false,{value=0}),t1,t2)))
								| (Impl(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,true,{value=0}),Beta(Node(q2,false,{value=0}),t1,t2)))
								(* Beta nodes *)
								| (And(q1,q2),false)-> Beta(Node(p,b,s),Beta(Node(q1,false,{value=0}),t1,t2),Beta(Node(q2,false,{value=0}),t1,t2))
								| (Or(q1,q2),true) -> Beta(Node(p,b,s),Beta(Node(q1,true,{value=0}),t1,t2),Beta(Node(q2,true,{value=0}),t1,t2))
								| (Impl(q1,q2),true) -> Beta(Node(p,b,s),Beta(Node(q1,false,{value=0}),t1,t2),Beta(Node(q2,true,{value=0}),t1,t2))
								(* Iff node *)
								| (Iff(q1,q2),true) -> Beta(Node(p,b,s),
															Alpha(Node(q1,true,{value=0}),Beta(Node(q2,true,{value=0}),t1,t2)),
															Alpha(Node(q1,false,{value=0}),Beta(Node(q2,false,{value=0}),t1,t2)))
								| (Iff(q1,q2),false) -> Beta(Node(p,b,s),
															Alpha(Node(q1,true,{value=0}),Beta(Node(q2,false,{value=0}),t1,t2)),
															Alpha(Node(q1,false,{value=0}),Beta(Node(q2,true,{value=0}),t1,t2)))
								(* Leaf Nodes *)
								| (L(st),_) -> t
								| (Not(q),_) -> Beta(Node(q,not b,{value =0}),t1,t2)
								| (T,true) -> t
								| (F,false) -> t
							)
;;

let rec step_develop t = match t with
						| Leaf(Node(p,b,s)) -> if (s.value = 2) then (expand t) else t
						| Alpha(Node(p,b,s),t1)->	if (s.value = 2) then (expand t)
													else Alpha(Node(p,b,s),step_develop t1)
						| Beta(Node(p,b,s),t1,t2) ->	if (s.value = 2) then (expand t)
														else Beta(Node(p,b,s),step_develop t1,step_develop t2)
;;


let rec full_develop t = 	
	let (t0) = contrad_path t (Hashtbl.create 10) in 
	let (b1,t1) = select_node t0 in
	let (t2) = step_develop t1 in 
	if b1 then full_develop t2 else t2	
;;


(* let find_assignments t = let t0 = full_develop t in
	let rec fa rho
 *)
(* let rec check_tautology t = *)

(* let rec check_contradiction t =  *)


(* Select Node *)
select_node (Leaf(Node(Or(L("p"),L("q")),true,{value=0})));;
select_node (Leaf(Node(And(L("p"),L("q")),true,{value=0})));;
select_node (Leaf(Node(Or(T,F),true,{value=2})));;


(* Testing Step develop *)
step_develop (Leaf(Node(Or(L("p"),L("q")),true,{value=2})));;
step_develop (Leaf(Node(And(L("p"),L("q")),true,{value=2})));;
step_develop (Leaf(Node(Or(T,F),true,{value=2})));;


(* Testing Contrad Path *)
contrad_path (Leaf(Node(T,true,{value = 0}))) (Hashtbl.create 1234);;
contrad_path (step_develop (Leaf(Node(Or(T,F),true,{value=0})))) (Hashtbl.create 12);;
contrad_path (step_develop (Leaf(Node(Or(T,F),true,{value=2})))) (Hashtbl.create 12);;
contrad_path (step_develop (Leaf(Node(And(L("p"),L("q")),true,{value=2})))) (Hashtbl.create 12);;

(* full develop *)
full_develop (Leaf(Node(Or(L("p"),L("q")),true,{value=0})));;
full_develop (Leaf(Node(And(L("p"),L("q")),true,{value=0})));;
full_develop (Leaf(Node(Or(T,F),true,{value=2})));; 


let t1 = (Or(And(L("A"),T),Impl(L("B"),L("A"))));;
let t2 = Iff(Not(Or(L("A"),L("B"))),And(Not(L("A")),Not(L("B"))));;
let t3 =	And(And (Or (Or (L "A", L "B"), Not (L "B")),Or (Not (L "A"), Or (L "A", L "B"))),
			And (Or (Or (L "A", L "B"), Not (L "B")), Or (Not (L "A"), Or (L "A", L "B"))));;

full_develop (Leaf(Node(t1,true,{value =0})));;
full_develop (Leaf(Node(t2,true,{value =0})));;
full_develop (Leaf(Node(t3,true,{value =0})));;
full_develop (Leaf(Node(t1,false,{value =0})));;
full_develop (Leaf(Node(t2,false,{value =0})));;
full_develop (Leaf(Node(t3,false,{value =0})));;
