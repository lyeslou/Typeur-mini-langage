(*
Lounis Lyes

Galou Arezki

*)

type lterme =
  | Var of string
  | Abs of string * lterme
  | App of lterme * lterme
  | Add of lterme * lterme
  | Sub of lterme * lterme
  | Cons of lterme * lterme
  | Hd of lterme 
  | Tl of lterme 
  | LetIn of string * lterme * lterme
  | BZ of lterme * lterme * lterme
  | BE of lterme * lterme * lterme
  | Nat of int
  | Fix of string * lterme

type stype =
  | Tvar of string
  | Fleche of stype * stype
  | Tint 
  | Liste of stype
  | Forall of string * stype

type tequa = Equa of stype * stype

let c = ref 0;;

let guess = Tvar "???";;

let gensym s =  (c:=!c+1 ;s^(string_of_int !c)) ;;
let reset () = c := 0;;




let rec print_lterme lt =
   match lt with
  Var x -> x
  |Abs (x, t) -> "(lambda "^x^"." ^ print_lterme t ^")"
  |App (lt1, lt2) -> "(" ^ print_lterme (lt1) ^" "^print_lterme (lt2)^")"
  |BZ(c,t,e) -> "(if0" ^ print_lterme (c) ^" then "^print_lterme (t)^" else"^ print_lterme (e)^")"
  |BE(c,t,e) -> "(ife" ^ print_lterme (c) ^" then "^print_lterme (t)^" else"^ print_lterme (e)^")"
  |LetIn(var, e1, e2) -> "(let " ^var^" ="^ print_lterme (e1)^" in"^ print_lterme (e2)^")"
  |Hd t -> "(head " ^ print_lterme (t)
  |Tl t -> "(tl " ^ print_lterme (t)
  |Cons (t1, t2) -> "(" ^ print_lterme (t1) ^" :: "^print_lterme (t2)^")"
  |Add (t1, t2) -> "(" ^ print_lterme(t1) ^" + "^ print_lterme(t2)^")"
  |Sub (t1, t2) -> "(" ^ print_lterme(t1) ^" + "^ print_lterme(t2)^")"
  |Nat n -> string_of_int n
  |_ -> ""

  ;;

  let substitue v ts t =
    let rec loop t =
      match t with
      |Tvar x -> if x = v then ts else Tvar x
      |Fleche (g,d) -> Fleche(loop g, loop d) 
      |Tint -> Tint
      |Liste l -> Liste(loop l)
      |Forall (x,res) -> Forall(x, loop res)
      
    in loop t
   
  ;;
  

  let rec type_egale t1 t2 =
    match t1, t2 with
    | (Tvar a, Tvar b) -> a = b 
    | (Fleche(a1, r1), Fleche(a2, r2)) -> type_egale a1 a2 && type_egale r1 r2
    | (Tint , Tint) -> true
    | (Liste a, Liste b) -> type_egale a b
    | (Forall (a, t1), Forall(b, t2)) -> 
      let newT = gensym "a" in 
        type_egale (substitue a (Tvar newT) t1) (substitue b (Tvar newT) t2)
    |_ -> false
  ;;      
  

let rec print_type t =
  match t with
  Tvar v -> v
  | Fleche (arg, res) -> "(" ^ print_type (arg) ^ "->"^print_type(res) ^")"
  | Tint-> "N"
  | Liste t -> "[" ^ print_type (t) ^"]"
  | Forall (a, t) -> "V"^a^"."^print_type t
;;

let sup_var v liste =
  let rec loop l res=
    match l with
    | [] -> res
    | x::xs -> if x=v then xs@res else loop xs (x::res)
  in loop liste [] 

let vars_libres typ =
  let rec loop typ res =
    match typ with
    |Tvar v -> v::res
    |Tint -> res
    |Liste x -> loop x res
    |Forall(x,t) -> let r = loop t res in sup_var x r
    |Fleche(a1,a2) -> let r1 = loop a1 res and r2 = loop a2 [] 
      in let rec loop2 r2 acc=
      match r2 with
      |[] -> acc
      |x::xs ->  loop2 xs (x::(sup_var x acc))
      in loop2 r2 r1
  in loop typ []
;;

let generalise envi typ =
  let rec loop libres acc =
    match libres with
    |[] -> acc
    |x::xs -> loop xs (Forall(x,acc))
  in loop (vars_libres typ) typ 
;;

let rec occur_check v typ =
  match typ with
  Tvar x -> v=x
  |Fleche (a1, a2) -> occur_check v a1 || occur_check v a2
  |Liste l -> occur_check v l
  |Forall(x, corps) -> occur_check v corps
  | Tint -> false


let barendreg typ =
  let rec loop typ map =
    match typ with
    |Tint -> Tint
    |Tvar v as tv-> (try Tvar (List.assoc v map) with _ ->  tv)
    |Fleche (arg, res) -> Fleche(loop arg map, loop res map)
    |Liste l -> Liste(loop l map)
    |Forall(x, corps) -> let newVar = gensym "v" in
      Forall(newVar,loop corps ((x,newVar)::map ))
  in loop typ []
;;

let substitue_partout v ts eq =
  let rec loop eq res =
    match eq with
    | [] -> res
    | Equa (g, d)::eqs-> loop eqs (Equa(substitue v ts g, substitue v ts d)::res)
    in loop eq []
;;


(*
Quand on avance on garde les equations dans res
Quand on recommence on concatene le reste d equations a verifier (equas) avec res
*)
let rec unification equas res =
  match equas with
  |[] -> res
  |(Equa(g, d) as eq) :: eqs -> 
  if g=d then unification (eqs@res) [] 
  else 
    match (g, d) with
    
    |(Forall(x, corps),_) -> let t1 = barendreg corps in
      let e = Equa(t1, d) in unification (e::eqs@res) []
    |(_, Forall(x, corps)) -> let t1 = barendreg corps in
      let e = Equa(g, t1) in unification (e::eqs@res) [] 
    |(Tvar x, _) -> if Tvar x=guess then unification eqs (eq::res)
      else if occur_check x d then []
      else unification (substitue_partout x d (eqs@res))  []
    |(_, Tvar x) ->if Tvar x=guess then unification eqs (eq::res)
      else if occur_check x g then []
      else unification (substitue_partout x g eqs@res)  []
    |(Fleche(ga, gr),Fleche(da, dr)) -> unification ( (Equa(ga, da)) :: (Equa(gr, dr))::eqs@res ) []
    
    
    |(Liste l1, Liste l2) -> unification (Equa(l1, l2)::eqs@res) [] 
    |_ -> [] 
    ;;
  
(* Si une etape retourne liste vide donc echoué 
*)
let rec gen_equas envi terme =
  let rec loop envi terme typ =
    match terme with
    | Var v -> Equa (typ, List.assoc v envi)::[]
    | Abs (v, corps) ->
        let ta = gensym "a" and tr = gensym "a" in
          let res = loop ((v, (Tvar ta))::envi) corps (Tvar tr) in
            if res = [] then []
            else (Equa (typ, Fleche (Tvar ta, Tvar tr))) :: res  
            
    | App(m1, m2) ->  
        let ta = gensym "a" in
        let res1 = (loop envi m1 (Fleche (Tvar ta, typ)) ) and res2 = loop envi m2 (Tvar ta)
          in if res1 = [] || res2 =[] then [] else (res1@res2) 
          
    | Fix(f, corps) -> 
        let tf = gensym "a" in
            let res = loop ((f,Tvar tf)::envi) corps (Tvar tf) in
              if res = [] then []
              else (Equa(typ, Tvar tf))::res
    | Nat n -> (Equa (typ, Tint))::[]
    | Add(_, _) -> Equa (typ, (Fleche(Tint, Fleche(Tint, Tint))) ) :: []
    | Sub(_, _) -> Equa (typ, (Fleche(Tint, Fleche(Tint, Tint))) ) :: []
    | Hd _ -> let newVar = gensym "a" in 
        Equa(typ, Forall(newVar, Fleche((Liste (Tvar newVar), Tvar newVar))))::[]
    | Tl _ -> let newVar = gensym "a" in 
        Equa(typ, Forall(newVar, Fleche((Liste (Tvar newVar), Liste (Tvar newVar)))))::[]
    | Cons _ -> let newVar = gensym "a" in 
        Equa(typ, Forall(newVar, Fleche(Tvar newVar, Fleche(Liste (Tvar newVar), Liste (Tvar newVar)) ) ) )::[]
    | BZ (c,th,els) -> let resC = loop envi c (Tint) and resTh = loop envi th typ and resEls = loop envi els typ in
        if resC = [] || resTh = [] || resEls = [] then [] else (resC@resTh@resEls)  
    
    | BE (c,th,els) -> let newVar = gensym "a" in let resC = loop envi c (Forall(newVar, Liste(Tvar newVar))) and resTh = loop envi th typ and resEls = loop envi els typ in
        if resC = [] || resTh = [] || resEls = [] then [] else (resC@resTh@resEls)  
    | LetIn(x,e1,e2) -> let res = typeur envi e1 in 
        let res2 = loop ( (x, (generalise envi res))::envi) e2 typ in
            res2 

  in loop envi terme guess
  
and typeur envi terme =
    let rec loop xs =
      match xs with
      |[] -> failwith "non typable"
      | (Equa(g, res))::xs -> if g = guess then res else if res = guess then g else loop xs 
    in loop (unification (gen_equas envi terme) [])
;;
  

let rec print_equas liste =
  match liste with
  [] -> "  "
  |(Equa (g, d)):: es -> print_type g ^ " = " ^ print_type d ^ print_equas es^"   "
;;










let ex1 =  (App(App(Abs("x", Var "x"), Abs("x", Var "x")), Nat 4 ) );;
print_string ("\n "^print_lterme ex1^" est de type : "^print_type ( (typeur [] (ex1 ) ) ))  ;;


let ex2 = (LetIn("f",Abs("x", Var "x"), Nat 3 ) ) ;;
print_string ("\n "^print_lterme ex2^" est de type : "^print_type ( (typeur [] (ex2 ) ) ))  ;;





