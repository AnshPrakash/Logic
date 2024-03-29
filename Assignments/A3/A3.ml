(* Natural Deduction Proof System *)

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


type dedtree =  Hyp of entails                                  | 
                T_I of entails                                  |
                Imp_I of  dedtree* entails                      |
                Imp_E of dedtree* dedtree* entails              |
                Not_I of dedtree* entails                       |
                Not_Classic of dedtree* entails                 |
                And_I of dedtree* dedtree* entails              |
                And_El of dedtree* entails                      |
                And_Er of dedtree* entails                      |
                Or_Il of dedtree* entails                       |
                Or_Ir of dedtree* entails                       |
                Or_E  of dedtree* dedtree* dedtree* entails
;;


let rec check_assumption assumptions p =
    match assumptions with
    | Assum([]) -> false
    | Assum(hd::tl) -> (isSame p hd) || check_assumption (Assum(tl)) p
;;



let rec pad proof props =
    match proof with
    |Hyp(Entails(Assum(l),p)) ->  Hyp(Entails(Assum(l@props),p))
    |T_I(Entails(Assum(l),p)) ->  T_I(Entails(Assum(l@props),p))
    |Imp_I(dpf,Entails(Assum(l),p)) -> Imp_I(pad dpf props, Entails(Assum(l@props),p))
    |Imp_E(dpf1,dpf2,Entails(Assum(l),p)) -> Imp_E(pad dpf1 props,pad dpf2 props,Entails(Assum(l@props),p))
    |Not_I(dpf,Entails(Assum(l),p)) -> Not_I(pad dpf props,Entails(Assum(l@props),p))
    |Not_Classic(dpf,Entails(Assum(l),p)) -> Not_Classic(pad dpf props,Entails(Assum(l@props),p))
    |And_I(dpf1,dpf2,Entails(Assum(l),p)) -> And_I(pad dpf1 props, pad dpf2 props, Entails(Assum(l@props),p))
    |And_El(dpf,Entails(Assum(l),p)) -> And_El(pad dpf props, Entails(Assum(l@props),p))
    |And_Er(dpf,Entails(Assum(l),p)) -> And_Er(pad dpf props, Entails(Assum(l@props),p))
    |Or_Il(dpf,Entails(Assum(l),p)) -> Or_Il(pad dpf props, Entails(Assum(l@props),p))
    |Or_Ir(dpf,Entails(Assum(l),p)) -> Or_Ir(pad dpf props, Entails(Assum(l@props),p))
    |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),p)) -> Or_E(pad dpf1 props, pad dpf2 props, pad dpf3 props, Entails(Assum(l@props),p))
;;
    


let rec getbases dpftree  = 
    match dpftree with
    |Hyp(Entails(Assum(l),p)) -> p::[]
    |T_I(Entails(Assum(l),p)) -> []
    |Imp_I(dpf,e)             -> getbases dpf
    |Imp_E(dpf1,dpf2,e)       -> (getbases dpf1)@(getbases dpf2)
    |Not_I(dpf,e)             -> getbases dpf
    |Not_Classic(dpf,e)       -> getbases dpf
    |And_I(dpf1,dpf2,e)       -> (getbases dpf1)@(getbases dpf2)
    |And_El(dpf,e)            -> getbases dpf
    |And_Er(dpf,e)            -> getbases dpf
    |Or_Il(dpf,e)             -> getbases dpf
    |Or_Ir(dpf,e)             -> getbases dpf
    |Or_E(dpf1,dpf2,dpf3,e)   -> (getbases dpf1)@(getbases dpf2)@(getbases dpf3)
;;


let rec is_element p assm = 
    match assm with
    | Assum([]) -> false
    | Assum(hd::tl) -> (isSame hd p) || is_element p (Assum(tl))
;;


let setify gamma = 
    let rec stif proplist setified =
    (   match proplist with
        | [] -> setified
        | hd::tl ->  if (is_element hd (Assum(tl))) then (stif tl (setified)) else (stif tl (hd::setified))
    ) in  (stif gamma ([]))
;;







let get_entails ndtree =
    match ndtree with
    |Hyp(e)                 -> e
    |T_I(e)                 -> e
    |Imp_I(dpf,e)           -> e
    |Imp_E(dpf1,dpf2,e)     -> e
    |Not_I(dpf,e)           -> e
    |Not_Classic(dpf,e)     -> e
    |And_I(dpf1,dpf2,e)     -> e
    |And_El(dpf,e)          -> e
    |And_Er(dpf,e)          -> e
    |Or_Il(dpf,e)           -> e
    |Or_Ir(dpf,e)           -> e
    |Or_E(dpf1,dpf2,dpf3,e) -> e
;;


let rec valid_ndprooftree proof = 
    match proof with
    |Hyp(Entails(Assum(l),p))                 -> check_assumption (Assum(l)) p
    |T_I(Entails(Assum(l),p))                 -> if p = T then true else false
    |Imp_I(dpf,Entails(Assum(l),Impl(p,q)))   -> 
        (   let Entails(assum,r) = get_entails dpf in 
            if (is_element p assum) && not (is_element p (Assum(l))) && (isSame r q) then (valid_ndprooftree dpf)
            else false
        )
    |Imp_E(dpf1,dpf2,Entails(Assum(l),q))     -> 
        (   try(
                let Entails(_,Impl(p1,q1)) = get_entails dpf1 in (
                    let Entails(_,p2) = get_entails dpf2 in 
                    (if (isSame p1 p2) && (isSame q1 q) then ((valid_ndprooftree dpf1) && (valid_ndprooftree dpf2)) else false)
                )
            )
            with _ -> false
        )
    |Not_I(dpf,Entails(Assum(l),p))           -> 
        (
            let Entails(assum,q) = get_entails dpf in (
                if q = F then valid_ndprooftree dpf else false
            )
        )
    |Not_Classic(dpf,Entails(Assum(l),p))     -> 
        (
            let Entails(assum, c)  = get_entails dpf in (
            (if (isSame c F) && (is_element (Not(p)) assum) && not (is_element (Not(p)) (Assum(l)))  then (valid_ndprooftree dpf) else false)
            )        
        )
    |And_I(dpf1,dpf2,Entails(Assum(l),And(p,q))) -> 
        (
            let Entails(_,p1) = get_entails dpf1 in (
            let Entails(_,q1) = get_entails dpf2 in(
            if (isSame p1 p) && (isSame q1 q) then (valid_ndprooftree dpf1) && (valid_ndprooftree dpf2) else false))
        )

    |And_El(dpf,Entails(Assum(l),p))          -> 
        (   try(
                let Entails(_,And(p1,q1)) = get_entails dpf in ( 
                if (isSame p1 p) then (valid_ndprooftree dpf) else false
                )
            )
            with _ -> false
        )

    |And_Er(dpf,Entails(Assum(l),q))          ->
        (   
            try(
                let Entails(_,And(p1,q1)) = get_entails dpf in ( 
                if (isSame q1 q) then (valid_ndprooftree dpf) else false
                )
            )
            with _ -> false
        )
    |Or_Il(dpf,Entails(Assum(l),Or(p,q)))           -> 
        (   
            try(
                let Entails(_,p1) = get_entails dpf in ( 
                if (isSame p1 p) then (valid_ndprooftree dpf) else false
                )
            )
            with _ -> false
        )
    |Or_Ir(dpf,Entails(Assum(l),Or(p,q)))           -> 
        (   
            try(
                let Entails(_,q1) = get_entails dpf in ( 
                if (isSame q1 q) then (valid_ndprooftree dpf) else false
                )
            )
            with _ -> false
        )
    |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),r)) -> 
        (   
            try(
                let Entails(assum1,Or(p,q)) = get_entails dpf1 in (
                let Entails(assum2,r1) = get_entails dpf2 in(
                let Entails(assum3,r2) = get_entails dpf3 in(
                    if (is_element p assum2) && (is_element q assum3) && (isSame r1 r2) && (isSame r1 r) then 
                    ( (valid_ndprooftree dpf1) && (valid_ndprooftree dpf2) && (valid_ndprooftree dpf3) )
                    else  false
                ))))
            with _ -> false
        )
    | _ -> false
;;




let rec findproof prooflist prop =
    match prooflist with
    | [] -> raise (Not_Found("no proof for this prop in the given proof list"))
    | hd::tl -> 
        (match hd with
        |Hyp(Entails(Assum(l),p))                 -> if isSame p prop then hd else findproof tl prop
        |T_I(Entails(Assum(l),p))                 -> if isSame p prop then hd else findproof tl prop
        |Imp_I(dpf,Entails(Assum(l),p))           -> if isSame p prop then hd else findproof tl prop
        |Imp_E(dpf1,dpf2,Entails(Assum(l),p))     -> if isSame p prop then hd else findproof tl prop
        |Not_I(dpf,Entails(Assum(l),p))           -> if isSame p prop then hd else findproof tl prop
        |Not_Classic(dpf,Entails(Assum(l),p))     -> if isSame p prop then hd else findproof tl prop
        |And_I(dpf1,dpf2,Entails(Assum(l),p))     -> if isSame p prop then hd else findproof tl prop
        |And_El(dpf,Entails(Assum(l),p))          -> if isSame p prop then hd else findproof tl prop
        |And_Er(dpf,Entails(Assum(l),p))          -> if isSame p prop then hd else findproof tl prop
        |Or_Il(dpf,Entails(Assum(l),p))           -> if isSame p prop then hd else findproof tl prop
        |Or_Ir(dpf,Entails(Assum(l),p))           -> if isSame p prop then hd else findproof tl prop
        |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),p)) -> if isSame p prop then hd else findproof tl prop
        )
;;


(* check if g1 is subset of g2 *)
let rec assumption_subset g1 g2 = 
    match g1 with
    | Assum([]) -> true
    | Assum(hd::tl) -> (is_element hd g2) && assumption_subset (Assum(tl)) g2
;;


let isEqualAssum g1 g2 = (assumption_subset g1 g2) && (assumption_subset g2 g1);;


(* correct gamma for the extended proof in grafting *)
let rec subst ndproof vgammal  =
    match ndproof with
    |Hyp(Entails(Assum(l),p))                 -> Hyp(Entails(Assum(vgammal),p))
    |T_I(Entails(Assum(l),p))                 -> T_I(Entails(Assum(vgammal),p))
    |Imp_I(dpf,Entails(Assum(l),Impl(p,q)))   -> Imp_I(subst dpf (p::vgammal),Entails(Assum(vgammal),Impl(p,q)))
    |Imp_E(dpf1,dpf2,Entails(Assum(l),p))     -> Imp_E(subst dpf1 vgammal,subst dpf2 vgammal,Entails(Assum(vgammal),p))
    |Not_I(dpf,Entails(Assum(l),p))           -> Not_I(subst dpf vgammal,Entails(Assum(vgammal),p))
    |Not_Classic(dpf,Entails(Assum(l),p))     -> Not_Classic(subst dpf ((Not(p))::vgammal),Entails(Assum(vgammal),p))
    |And_I(dpf1,dpf2,Entails(Assum(l),p))     -> And_I(subst dpf1 vgammal,subst dpf2 vgammal,Entails(Assum(vgammal),p))
    |And_El(dpf,Entails(Assum(l),p))          -> And_El(subst dpf vgammal,Entails(Assum(vgammal),p))
    |And_Er(dpf,Entails(Assum(l),p))          -> And_Er(subst dpf vgammal,Entails(Assum(vgammal),p))
    |Or_Il(dpf,Entails(Assum(l),p))           -> Or_Il(subst dpf vgammal,Entails(Assum(vgammal),p))
    |Or_Ir(dpf,Entails(Assum(l),p))           -> Or_Ir(subst dpf vgammal,Entails(Assum(vgammal),p))
    |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),r)) -> 
        (
            let Entails(_,Or(p,q)) = get_entails dpf1 in
            Or_E(subst dpf1 vgammal,subst dpf2 (p::vgammal),subst dpf3 (q::vgammal),Entails(Assum(vgammal),r))
        )
;;


(* extend the proof on leafs *)
let rec substpf ndproof prooflist = 
    match ndproof with
    |Hyp(Entails(Assum(l),p))                 -> 
        (   try(
               let newproof = findproof prooflist p in newproof
            )
            with Not_Found(err) -> ndproof
        )
    |T_I(Entails(Assum(l),p))                 -> T_I(Entails(Assum(l),p))
    |Imp_I(dpf,Entails(Assum(l),p))           -> Imp_I(substpf dpf prooflist,Entails(Assum(l),p))
    |Imp_E(dpf1,dpf2,Entails(Assum(l),p))     -> Imp_E(substpf dpf1 prooflist,substpf dpf2 prooflist,Entails(Assum(l),p))
    |Not_I(dpf,Entails(Assum(l),p))           -> Not_I(substpf dpf prooflist,Entails(Assum(l),p))
    |Not_Classic(dpf,Entails(Assum(l),p))     -> Not_Classic(substpf dpf prooflist,Entails(Assum(l),p))
    |And_I(dpf1,dpf2,Entails(Assum(l),p))     -> And_I(substpf dpf1 prooflist,substpf dpf2 prooflist,Entails(Assum(l),p))
    |And_El(dpf,Entails(Assum(l),p))          -> And_El(substpf dpf prooflist,Entails(Assum(l),p))
    |And_Er(dpf,Entails(Assum(l),p))          -> And_Er(substpf dpf prooflist,Entails(Assum(l),p))
    |Or_Il(dpf,Entails(Assum(l),p))           -> Or_Il(substpf dpf prooflist,Entails(Assum(l),p))
    |Or_Ir(dpf,Entails(Assum(l),p))           -> Or_Ir(substpf dpf prooflist,Entails(Assum(l),p))
    |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),p)) -> Or_E(substpf dpf1 prooflist,substpf dpf2 prooflist,substpf dpf3 prooflist,Entails(Assum(l),p))
;;

let getgamma lt = 
    match lt with
    | [] -> []
    | hd::tl -> (let Entails(Assum(ll),_) = (get_entails hd) in ll)
;;


let graft ndproof prooflist =
    let extendpf = substpf ndproof prooflist in
    let vgamma = getgamma prooflist in
    subst extendpf vgamma
;;



let rec rsubset cur_set base_set =
	match cur_set with
	| [] -> []
	| hd::tl -> if is_element (hd) (Assum(base_set)) then hd::(rsubset tl base_set) else rsubset tl base_set
;;
	


let rec prune prooft = 
    let base_set = setify (getbases prooft) in 
	let r_gam = getgamma ([prooft]) in
	let subprops  = rsubset r_gam base_set in
	subst prooft subprops
;;


(* Test Case *)

let p = L("p");;
let q = L("q");;
let r = L("r");;
let pf1 = Imp_I(
	Imp_I(
		Imp_I(
			Imp_E(
					Imp_E(Hyp(Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),Impl(p,Impl(q,r))))
						,Hyp(Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),p))
						,Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),Impl(q,r)))
				,Imp_E(Hyp(Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),Impl(p,q)))
					,Hyp(Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),p))
					,Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),q))
				,Entails(Assum([Impl(p,Impl(q,r));Impl(p,q);p]),r))
			,Entails(Assum([Impl(p,Impl(q,r));Impl(p,q)]),Impl(p,r)))
		,Entails(Assum([Impl(p,Impl(q,r))]) ,Impl(Impl(p,q),Impl(p,r)) ) )
	,
Entails(Assum([]),Impl(Impl(p,Impl(q,r)),Impl(Impl(p,q),Impl(p,r)))));;

valid_ndprooftree pf1;;

let k = L("k");;
let assuml = [k;Impl(k,k);Impl(F,T)];;


let pf2 = pad pf1 assuml;;

valid_ndprooftree (pad pf1 assuml);;

let pf3 = prune pf2;;
valid_ndprooftree pf3;;

