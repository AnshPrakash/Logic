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






