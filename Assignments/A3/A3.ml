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




let rec prune prooft = 
    let subprops = setify (getbases prooft) in 
    let rec replace dproof newprops =
    (   match dproof with
        |Hyp(Entails(Assum(l),p))                 -> Hyp(Entails(Assum(newprops),p))
        |T_I(Entails(Assum(l),p))                 -> T_I(Entails(Assum(newprops),p))
        |Imp_I(dpf,Entails(Assum(l),p))           -> Imp_I(replace dpf newprops, Entails(Assum(newprops),p))
        |Imp_E(dpf1,dpf2,Entails(Assum(l),p))     -> Imp_E(replace dpf1 newprops,replace dpf2 newprops,Entails(Assum(newprops),p))
        |Not_I(dpf,Entails(Assum(l),p))           -> Not_I(replace dpf newprops,Entails(Assum(newprops),p))
        |Not_Classic(dpf,Entails(Assum(l),p))     -> Not_Classic(replace dpf newprops,Entails(Assum(newprops),p))
        |And_I(dpf1,dpf2,Entails(Assum(l),p))     -> And_I(replace dpf1 newprops, replace dpf2 newprops, Entails(Assum(newprops),p))
        |And_El(dpf,Entails(Assum(l),p))          -> And_El(replace dpf newprops, Entails(Assum(newprops),p))
        |And_Er(dpf,Entails(Assum(l),p))          -> And_Er(replace dpf newprops, Entails(Assum(newprops),p))
        |Or_Il(dpf,Entails(Assum(l),p))           -> Or_Il(replace dpf newprops, Entails(Assum(newprops),p))
        |Or_Ir(dpf,Entails(Assum(l),p))           -> Or_Ir(replace dpf newprops, Entails(Assum(newprops),p))
        |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),p)) -> Or_E(replace dpf1 newprops, replace dpf2 newprops, replace dpf3 newprops, Entails(Assum(newprops),p))
    ) in (replace prooft subprops)
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


let rec graft ndproof prooflist = 
    match ndproof with
    |Hyp(Entails(Assum(l),p))                 -> 
        (   try(
               let newproof = findproof prooflist p in newproof
            )
            with Not_Found(err) -> ndproof
        )
    |T_I(Entails(Assum(l),p))                 -> ndproof
    |Imp_I(dpf,Entails(Assum(l),p))           -> Imp_I(graft dpf prooflist,Entails(Assum(l),p))
    |Imp_E(dpf1,dpf2,Entails(Assum(l),p))     -> Imp_E(graft dpf1 prooflist,graft dpf2 prooflist,Entails(Assum(l),p))
    |Not_I(dpf,Entails(Assum(l),p))           -> Not_I(graft dpf prooflist,Entails(Assum(l),p))
    |Not_Classic(dpf,Entails(Assum(l),p))     -> Not_Classic(graft dpf prooflist,Entails(Assum(l),p))
    |And_I(dpf1,dpf2,Entails(Assum(l),p))     -> And_I(graft dpf1 prooflist,graft dpf2 prooflist,Entails(Assum(l),p))
    |And_El(dpf,Entails(Assum(l),p))          -> And_El(graft dpf prooflist,Entails(Assum(l),p))
    |And_Er(dpf,Entails(Assum(l),p))          -> And_Er(graft dpf prooflist,Entails(Assum(l),p))
    |Or_Il(dpf,Entails(Assum(l),p))           -> Or_Il(graft dpf prooflist,Entails(Assum(l),p))
    |Or_Ir(dpf,Entails(Assum(l),p))           -> Or_Ir(graft dpf prooflist,Entails(Assum(l),p))
    |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),p)) -> Or_E(graft dpf1 prooflist,graft dpf2 prooflist,graft dpf3 prooflist,Entails(Assum(l),p))
;;
