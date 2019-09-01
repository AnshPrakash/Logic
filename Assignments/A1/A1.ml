
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

let rec contrad_path t rho = match t with 
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


let rec select_node t = match t with
						| Leaf(Node(p,b,s)) -> if (s.value = 0) then (s.value <- 2; true) else false
						| Alpha(Node(p,b,s),t1) ->  if (s.value = 0) then (s.value <- 2; true) else select_node t1
						| Beta(Node(p,b,s),t1,t2) ->	if (s.value = 0) then (s.value <- 2; true) 
														else if (select_node t1) then true 
														else (select_node t2)
;;


let expand n = match n with
				|Node(p,b,s) -> (	s.value <- 1;
									match p with
									| T -> Leaf(n)
									| F -> Leaf(n)
									| Not(q) -> Leaf(Node(q,not b,s))
									| And(q1,q2) -> if b then Alpha(
																	Node(p,b,s),
																	Alpha( Node(q1,true,{value = 0}),
																		Leaf(Node(q2,true,{value = 0})))
																		)
													else Beta(Node(p,b,s),Leaf(Node(q1,false,{value = 0})),Leaf(Node(q2,false,{value = 0})))
									| Or(q1,q2) ->	if not b then Alpha(Node(p,b,s),
																	Alpha(
																		Node(q1,false,{value = 0}),
																		Leaf(Node(q2,false,{value = 0}))
																	))
													else Beta(Node(p,b,s),Leaf(Node(q1,true,{value = 0})),Leaf(Node(q2,true,{value = 0})))
									| Impl(q1,q2)->	if not b then Alpha(Node(p,b,s),
																	Alpha(
																		Node(q1,true,{value = 0}),
																		Leaf(Node(q2,false,{value = 0}))
																	)
																)
													else Beta(Node(p,b,s),Leaf(Node(q1,false,{value = 0})),Leaf(Node(q2,true,{value = 0})))
									| Iff(q1,q2) -> if b then Beta(Node(p,b,s),Alpha(Node(q1,true,{value =0})
																	,Leaf(Node(q2,true,{value =0})))
																	, Alpha(
																		
																			Node(q1,false,{value =0}),Leaf(Node(q2,false,{value =0})))
																		)
													else Beta(Node(p,b,s),Alpha(Node(q1,true,{value =0}),
																				Leaf(Node(q2,false,{value =0})))
																	, Alpha(Node(q1,false,{value =0}),Leaf(Node(q2,true,{value =0})))
																)
									| L(st) -> Leaf(n)
								)
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

(* let rec check_tautology t = *)

(* let rec check_contradiction t =  *)



contrad_path (Leaf(Node(T,true,{value = 0}))) (Hashtbl.create 1234);;


