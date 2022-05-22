
type exp = Const of int | Sub of exp * exp
type context = exp -> exp
(*@ invariant forall e1 e2 r1 r2.
      post self e1 r1 ->
      post self e2 r2 ->
      eval e1 = eval e2 ->
      eval r1 = eval r2 *)

(*@ predicate is_value (e : exp) =
match e with 
|Const _ -> true
|_ -> false
*)

(*@ predicate is_redex (e : exp) = 
match e with 
|Subst(Const _, Const _) -> true 
|_ -> false
*)

let rec decompose_term
  (e: exp) (c : context) : (context * exp)
= match e with
  | Sub (Const v1, Const v2) -> (c, e)
  | Sub (Const v, e) ->
      decompose_term e (fun
      (*@ ensures post c (Sub(Const v, x)) result*)
       x -> c (Sub(Const v, x)))
  | Sub (e1, e2) ->
      decompose_term e1 (fun
      (*@ ensures post c (Sub(x, e2)) result *)
       x -> c (Sub(x, e2)))
  |_ -> assert false
(*@ c_res, e_res = result
      requires not (is_value e)
      ensures  is_redex e_res &&
        forall res. post c e res ->
          post c_res e_res res *)

let decompose (e: exp) : context * exp =
  decompose_term e (fun x -> x)
(*@ let c_res, e_res = result in
      requires not (is_value e)
      ensures is_redex e_res &&
              post c_res e_res e *)


(*@ function eval (e : exp) = 
match e with
|Const v -> v
|Subst (e1, e2) -> eval e1 - eval e2 *)

let head_reduction e = 
  match e with 
  |Sub(Const v1, Const v2) -> Const (v1 - v2)
  |_ -> assert false 
(*@requires is_redex e
   eval result = eval e*)

let rec red (e : exp) : int =
  match e with
  | Const v -> v
  | _ ->
    let (c, r) = decompose e in
    let red_r =
     head_reduction r in red (c red_r)
(*@ ensures r = eval e *)
          
         
let () = Printf.printf "%d" (red (Sub (Sub(Const 1, Const 1), Const 2)))