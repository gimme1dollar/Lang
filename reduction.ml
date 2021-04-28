exception NotImplemented 
exception Stuck
open Uml

(* free_variable: x is in FV(e) *)
let rec is_free x e =
  let rec free_vars f =
    match f with
    | Var y -> [y]
    | Lam (y, f') ->
      let vars = free_vars f' in
      List.filter (fun v -> v <> y) vars
    | App (f1, f2) ->
      (free_vars f1) @ (free_vars f2)
  in
  List.mem x (free_vars e) 

let freshVarCounter = ref 0
let rec getFreshVariable s e x = 
  let _ = freshVarCounter := !freshVarCounter + 1 in
  let res = s ^ "__" ^ (string_of_int (!freshVarCounter)) in

  if (not (is_free res e)) && (not (is_free res x))
    then res
    else getFreshVariable res e x

(* substition: [e'/x]e *)
let rec substitute e' x e =
  (* variable swapping: [x <-> y] e *)
  let rec var_swap x y e =
    match e with 
    | Var z -> 
      if z = x then (Var y)
      else if z = y then (Var x)
      else (Var z)
    | Lam (z, e') -> 
      if z = x then Lam (y, (var_swap x y e'))
      else if z = y then Lam (x, (var_swap x y e'))
      else Lam (z, var_swap x y e')
    | App (e1, e2) -> 
      let e1_ = (var_swap x y e1) in
      let e2_ = (var_swap x y e2) in
      App (e1_, e2_)
  in

  match e with
  | Var y -> 
    if y = x
      then e'
      else e
  | App (e1, e2) -> 
    let e1' = substitute e' x e1 in
    let e2' = substitute e' x e2 in
    App (e1', e2')
  | Lam (y, f) -> 
    if y = x 
    then e
    else 
      if not (is_free y e')
      then 
        let f_  = substitute e' x f in 
        Lam(y, f_) 
      else 
        let z   = getFreshVariable y f e' in
        let f_  = var_swap y z f in
        let f__ = substitute e' x f_ in
        Lam(z, f__)

(* reduction using the call-by-value strategy. *)
let rec stepv e = 
  match e with
  | Var _ -> raise Stuck
  | Lam _ -> raise Stuck
  | App (e1, e2) -> 
    (
      match e1 with 
      | Var _ -> 
        App ((stepv e1), e2)
      | Lam (x1, e1') -> 
        (
          match e2 with
          | Var _ ->
            App (e1, (stepv e2))
          | Lam _ -> 
            substitute e2 x1 e1'
          | App _ ->
            App (e1, (stepv e2))
        )
      | App _ -> 
        App ((stepv e1), e2)      
    )