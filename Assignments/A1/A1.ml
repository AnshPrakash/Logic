module SS = Set.Make(String);;


type prop = T | F | L of string | Not of prop | And of prop*prop 
			| Or  of prop*prop | Impl of prop*prop | Iff of prop*prop
;;


exception Not_Found of string;;
exception Contrad;;


(*  -1:contradiction ,   0 :unexamined,  1: examined,   2:selected *)
type node = Node of prop*bool*int
;;

type tree = Leaf of node| Alpha of node*tree | Beta of node*tree*tree
;;

type example = LL of ((string*bool) list)
;;

type proof = P of tree | E of example
;;

let print_hash hash = Hashtbl.iter (fun x y -> Printf.printf "%s -> %b\n" x y) hash
;;


let update t assign = 	
	let helper p b s rho = (	if (s != -1) then 
									match p with
									| L(st) -> (try (if (Hashtbl.find rho st) != b then (raise Contrad) else rho)
												with Not_found -> let rho1 = Hashtbl.copy rho in (Hashtbl.add rho1 st b;rho1) )
									| T -> if (b = false) then raise Contrad else rho
									| F -> if (b = true) then raise Contrad else rho
									| _ -> rho
								else raise Contrad) in 
	(	match t with
	| Leaf(Node(p,b,s)) -> (helper p b s assign)
	| Alpha(Node(p,b,s),t1) -> (helper p b s assign)
	| Beta(Node(p,b,s),t1,t2) -> (helper p b s assign))
;;


let change_status t new_s = 
	match t with
	| Leaf(Node(p,b,s)) -> Leaf(Node(p,b,new_s))
	| Alpha(Node(p,b,s),t1) -> Alpha(Node(p,b,new_s),t1)
	| Beta(Node(p,b,s),t1,t2) -> Beta(Node(p,b,new_s),t1,t2)
;;

let rec contrad_path t rho =
	try (let rho1 = update t rho in
		(	match t with
			| Leaf(Node(p,b,s)) -> t
			| Alpha(Node(p,b,s),t1) -> Alpha(Node(p,b,s),contrad_path t1 rho1)
			| Beta(Node(p,b,s),t1,t2) -> (let rho1c = Hashtbl.copy rho1 in Beta(Node(p,b,s),contrad_path t1 rho1, contrad_path t2 rho1c))
		)
	)
	with Contrad -> change_status t (-1)
;;
	
let rec select_node t = match t with
						| Leaf(Node(p,b,s)) -> (if (s = 0) then (true,(change_status t (2))) else (false,t))
						| Alpha(Node(p,b,s),t1) ->  (	if (s = 0) then ((true,(change_status t (2)))) 
														else if (s != -1 ) then 
																(let (tb,tt1) = (select_node t1) in
																	(tb,Alpha(Node(p,b,s),tt1))
																)
														else (false,t)		
													)
						| Beta(Node(p,b,s),t1,t2) -> (	if (s = 0) then (true,(change_status t (2)))
														else if (s != -1) then
																(let (tb1,tt1) = select_node t1 in
																	(
																	if tb1 then (true,Beta(Node(p,b,s),tt1,t2))
																	else (let (tb2,tt2) = select_node t2 in
																			(tb2,Beta(Node(p,b,s),t1,tt2)))
																	)
																)
														else (false,t)
													)	
;;


let expand tt = let t = change_status tt 1 in
	match t with
	| Leaf(Node(p,b,s)) -> 	(
								match (p,b) with
								(* Alpha nodes *)
								| (And(q1,q2),true)-> Alpha(Node(p,b,s),Alpha(Node(q1,true,0),Leaf(Node(q2,true,0))))
								| (Or(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,false,0),Leaf(Node(q2,false,0))))
								| (Impl(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,true,0),Leaf(Node(q2,false,0))))
								(* Beta nodes *)
								| (And(q1,q2),false)-> Beta(Node(p,b,s),Leaf(Node(q1,false,0)),Leaf(Node(q2,false,0)))
								| (Or(q1,q2),true) -> Beta(Node(p,b,s),Leaf(Node(q1,true,0)),Leaf(Node(q2,true,0)))
								| (Impl(q1,q2),true) -> Beta(Node(p,b,s),Leaf(Node(q1,false,0)),Leaf(Node(q2,true,0)))
								(* Iff node *)
								| (Iff(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,true,0),Leaf(Node(q2,true,0)))
															, Alpha(Node(q1,false,0),Leaf(Node(q2,false,0)))
															)
								| (Iff(q1,q2),false) -> Beta(Node(p,b,s),Alpha(Node(q1,true,0),Leaf(Node(q2,false,0)))
															, Alpha(Node(q1,false,0),Leaf(Node(q2,true,0)))
															)
								(* Leaf Nodes *)
								| (L(st),_) -> t
								| (Not(q),_) -> Leaf(Node(q, not b,0))
								| (T,true) -> t
								| (F,false) -> t
							)
	| Alpha(Node(p,b,s),t1) -> (
								match (p,b) with
								(* Alpha nodes *)
								| (And(q1,q2),true)-> Alpha(Node(p,b,s),Alpha(Node(q1,true,0),Alpha(Node(q2,true,0),t1)))
								| (Or(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,false,0),Alpha(Node(q2,false,0),t1)))
								| (Impl(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,true,0),Alpha(Node(q2,false,0),t1)))
								(* Beta nodes *)
								| (And(q1,q2),false)-> Beta(Node(p,b,s),Alpha(Node(q1,false,0),t1),Alpha(Node(q2,false,0),t1))
								| (Or(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,true,0),t1),Alpha(Node(q2,true,0),t1))
								| (Impl(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,false,0),t1),Alpha(Node(q2,true,0),t1))
								(* Iff node *)
								| (Iff(q1,q2),true) -> Beta(Node(p,b,s),Alpha(Node(q1,true,0),Alpha(Node(q2,true,0),t1)),Alpha(Node(q1,false,0),Alpha(Node(q2,false,0),t1)))
								| (Iff(q1,q2),false) -> Beta(Node(p,b,s),Alpha(Node(q1,true,0),Alpha(Node(q2,false,0),t1)),Alpha(Node(q1,false,0),Alpha(Node(q2,true,0),t1)))
								(* Leaf Nodes *)
								| (L(st),_) -> t
								| (Not(q),_) -> Alpha(Node(q,not b,0),t1)
								| (T,true) -> t
								| (F,false) -> t
							)
	| Beta(Node(p,b,s),t1,t2) -> (
								match (p,b) with
								(* Alpha nodes *)
								| (And(q1,q2),true)-> Alpha(Node(p,b,s),Alpha(Node(q1,true,0),Beta(Node(q2,true,0),t1,t2)))
								| (Or(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,false,0),Beta(Node(q2,false,0),t1,t2)))
								| (Impl(q1,q2),false) -> Alpha(Node(p,b,s),Alpha(Node(q1,true,0),Beta(Node(q2,false,0),t1,t2)))
								(* Beta nodes *)
								| (And(q1,q2),false)-> Beta(Node(p,b,s),Beta(Node(q1,false,0),t1,t2),Beta(Node(q2,false,0),t1,t2))
								| (Or(q1,q2),true) -> Beta(Node(p,b,s),Beta(Node(q1,true,0),t1,t2),Beta(Node(q2,true,0),t1,t2))
								| (Impl(q1,q2),true) -> Beta(Node(p,b,s),Beta(Node(q1,false,0),t1,t2),Beta(Node(q2,true,0),t1,t2))
								(* Iff node *)
								| (Iff(q1,q2),true) -> Beta(Node(p,b,s),
															Alpha(Node(q1,true,0),Beta(Node(q2,true,0),t1,t2)),
															Alpha(Node(q1,false,0),Beta(Node(q2,false,0),t1,t2)))
								| (Iff(q1,q2),false) -> Beta(Node(p,b,s),
															Alpha(Node(q1,true,0),Beta(Node(q2,false,0),t1,t2)),
															Alpha(Node(q1,false,0),Beta(Node(q2,true,0),t1,t2)))
								(* Leaf Nodes *)
								| (L(st),_) -> t
								| (Not(q),_) -> Beta(Node(q,not b,0),t1,t2)
								| (T,true) -> t
								| (F,false) -> t
							)
;;

let rec step_develop t = 
	match t with
	| Leaf(Node(p,b,s)) -> if (s = 2) then (expand t) else t
	| Alpha(Node(p,b,s),t1)->	if (s = 2) then (expand t)
								else Alpha(Node(p,b,s),step_develop t1)
	| Beta(Node(p,b,s),t1,t2) ->	if (s = 2) then (expand t)
									else Beta(Node(p,b,s),step_develop t1,step_develop t2)
;;


let rec full_develop t = 	
	let (t0) = contrad_path t (Hashtbl.create 10) in 
	let (b1,t1) = select_node t0 in
	let (t2) = step_develop t1 in 
	if b1 then full_develop t2 else t1	
;;


let rec unique l = match l with
				| [] -> []
				| hd::tl -> if List.mem hd tl then unique tl else hd::(unique tl)
;;

let mycmp t1 t2 = let (s1,b1) = t1 in 
	let (s2,b2) = t2 in
	  if String.length s1 <> String.length s2 then
	    compare (String.length s2) (String.length s1)
	  else
	    String.compare (String.lowercase_ascii s1) (String.lowercase_ascii s2)
;;

let find_assignments t = let t0 = full_develop t in
	let rec fa tab rho = match tab with
					| Leaf(Node(p,b,s)) ->	if (s = -1) then []
											else (	match p with
														| L(st) -> [(st,b)::rho]
														| _ -> [rho]
													)
					| Alpha(Node(p,b,s),t1) ->	if (s = -1) then [] 
												else (	match p with
														| L(st) -> fa t1 ((st,b)::rho)
														| _ -> fa t1 rho
													)
					| Beta(Node(p,b,s),t1,t2)->	if (s = -1) then [] 
												else(	match p with
														| L(st) -> (fa t1 ((st,b)::rho))@(fa t2 ((st,b)::rho))
														| _ -> (fa t1 rho)@(fa t2 rho)
													)
	in let rhos = fa t0 [] in 
	unique (List.map unique (List.map (List.sort mycmp) rhos))
;;

(* p :propositon *)
let rec check_tautology p = let l = find_assignments (Leaf(Node(p,false,0))) in 
			match l with
			| [] -> P(full_develop (Leaf(Node(p,false,0))))
			| hd::tl-> E(LL(hd))
;;


let rec check_contradiction p = let l = find_assignments (Leaf(Node(p,true,0))) in 
			match l with
			| [] -> P(full_develop (Leaf(Node(p,true,0))))
			| hd::tl-> E(LL(hd))
;;



(* Select Node *)
select_node (Leaf(Node(Or(L("p"),L("q")),true,0)));;
select_node (Leaf(Node(And(L("p"),L("q")),true,0)));;
select_node (Leaf(Node(Or(T,F),true,2)));;


(* Testing Step develop *)
step_develop (Leaf(Node(Or(L("p"),L("q")),true,2)));;
step_develop (Leaf(Node(And(L("p"),L("q")),true,2)));;
step_develop (Leaf(Node(Or(T,F),true,2)));;


(* Testing Contrad Path *)
contrad_path (Leaf(Node(T,true,0))) (Hashtbl.create 1234);;
contrad_path (step_develop (Leaf(Node(Or(T,F),true,0)))) (Hashtbl.create 12);;
contrad_path (step_develop (Leaf(Node(Or(T,F),true,2)))) (Hashtbl.create 12);;
contrad_path (step_develop (Leaf(Node(And(L("p"),L("q")),true,2)))) (Hashtbl.create 12);;

(* full develop *)
full_develop (Leaf(Node(Or(L("p"),L("q")),true,0)));;
full_develop (Leaf(Node(And(L("p"),L("q")),true,0)));;
full_develop (Leaf(Node(Or(T,F),true,2)));; 


let t1 = (Or(And(L("A"),T),Impl(L("B"),L("A"))));;
let t2 = Iff(Not(Or(L("A"),L("B"))),And(Not(L("A")),Not(L("B"))));;
let t3 =	And(And (Or (Or (L "A", L "B"), Not (L "B")),Or (Not (L "A"), Or (L "A", L "B"))),
			And (Or (Or (L "A", L "B"), Not (L "B")), Or (Not (L "A"), Or (L "A", L "B"))));;

full_develop (Leaf(Node(t1,true,0)));;
full_develop (Leaf(Node(t2,true,0)));;
full_develop (Leaf(Node(t3,true,0)));;
full_develop (Leaf(Node(t1,false,0)));;
full_develop (Leaf(Node(t2,false,0)));;
full_develop (Leaf(Node(t3,false,0)));;

check_tautology t1 ;;
check_tautology t2 ;;
check_tautology t3 ;;


let t6 = T;;
let t7 = Or(L("p"),Not(L("p")));;
check_tautology t6 ;;
check_tautology t7;;

check_contradiction (Not(T));;
check_contradiction (And(t7,Not(t7)));;

full_develop (Leaf(Node((And(t7,Not(t7))),true,0)));;

let k =Alpha (Node (And (Or (L "p", Not (L "p")), Not (Or (L "p", Not (L "p")))), true,1),
		 Beta (Node (Or (L "p", Not (L "p")), true, 0),
  Alpha (Node (L "p", true,-1),
   Leaf (Node (Not (Or (L "p", Not (L "p"))), true, 0))),
						  Alpha (Node (L "p", false, 0),
						   Alpha (Node (Or (L "p", Not (L "p")), false,-1),
						    Alpha (Node (L "p", false, 0),
						     Leaf (Node (L "p", true, 0)))))))
;;

select_node k;;

find_assignments (Leaf(Node(k,false,0)));;

let t8 = Impl(L "p", L "p");;
let t9 = Impl(L "p", Impl(L "q", L "p"));;
check_tautology t8;;
check_tautology t9;;
