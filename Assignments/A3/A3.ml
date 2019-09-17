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
    |Imp_E(dpf1,dpf2,e)      -> (getbases dpf1)@(getbases dpf2)
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
        |Hyp(Entails(Assum(l),p)) ->  Hyp(Entails(Assum(newprops),p))
        |T_I(Entails(Assum(l),p)) ->  T_I(Entails(Assum(newprops),p))
        |Imp_I(dpf,Entails(Assum(l),p)) -> Imp_I(replace dpf newprops, Entails(Assum(newprops),p))
        |Imp_E(dpf1,dpf2,Entails(Assum(l),p)) -> Imp_E(replace dpf1 newprops,replace dpf2 newprops,Entails(Assum(newprops),p))
        |Not_I(dpf,Entails(Assum(l),p)) -> Not_I(replace dpf newprops,Entails(Assum(newprops),p))
        |Not_Classic(dpf,Entails(Assum(l),p)) -> Not_Classic(replace dpf newprops,Entails(Assum(newprops),p))
        |And_I(dpf1,dpf2,Entails(Assum(l),p)) -> And_I(replace dpf1 newprops, replace dpf2 newprops, Entails(Assum(newprops),p))
        |And_El(dpf,Entails(Assum(l),p)) -> And_El(replace dpf newprops, Entails(Assum(newprops),p))
        |And_Er(dpf,Entails(Assum(l),p)) -> And_Er(replace dpf newprops, Entails(Assum(newprops),p))
        |Or_Il(dpf,Entails(Assum(l),p)) -> Or_Il(replace dpf newprops, Entails(Assum(newprops),p))
        |Or_Ir(dpf,Entails(Assum(l),p)) -> Or_Ir(replace dpf newprops, Entails(Assum(newprops),p))
        |Or_E(dpf1,dpf2,dpf3,Entails(Assum(l),p)) -> Or_E(replace dpf1 newprops, replace dpf2 newprops, replace dpf3 newprops, Entails(Assum(newprops),p))
    ) in (replace prooft subprops)
;;





(*  
let rec valid_ndprooftree proof = 
    match proof with
    | Base(Entails(Assum(l),p)) -> (check_axiom p) || check_assumption (Assum(l)) p
    | MP(hp1,hp2,Entails(Assum(l),p)) -> (
            let e1,e2 = (get_entails hp1),(get_entails hp2) in (
                match e1,e2 with
                | (Entails(assu1,p1),Entails(assu2,p2))-> (
                        if  (isEqualAssum assu1 assu2) && (isEqualAssum assu1 (Assum(l))) then (
                            try (
                                    let (p1_1,p1_2) = split_impl p1 in (
                                    (isSame p1_1 p2) && (isSame p1_2 p) && (valid_hprooftree hp1) && (valid_hprooftree hp2)
                                )
                            )
                            with Not_Valid ->  false
                        )
                        else false
                    )
            )
        )
;;
 *)


(* let rec graft proof prooflist = 
    let newgamma = 
    (   match prooflist with
        | [] -> Assum([])
        | hd::tl -> getassum hd
    ) in (
    let rec subs htree =
    (
        match htree with
        | Base(Entails(Assum(l),p)) -> 
        (   try (
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
 *)