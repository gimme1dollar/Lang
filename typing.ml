open Tml

exception TypeError
type context = (var * tp) list

module type DICT =
  sig
    val empty : unit -> context
    val lookup : context -> var -> tp
    val delete : context -> var -> context
    val insert : context -> var -> tp -> context 
  end

module Context : DICT =
  struct
    let empty () = []

    let lookup (d : context) (k : var) = 
      let rec lookup_rec (d : context) (k : var) =
        match d with
        | [] -> raise TypeError
        | (d_head_key, d_head_value)::d_tails -> 
          if d_head_key = k 
            then d_head_value
            else lookup_rec d_tails k
      in
      lookup_rec d k

    let delete (d : context) (k : var) =
      let rec dfilterk (d : context) (k : var) acc = 
        match d with
        | [] -> acc
        | (d_head_key, d_head_value)::d_tails ->
            if (d_head_key = k) then dfilterk d_tails k acc
            else dfilterk d_tails k ((d_head_key, d_head_value)::acc)
      in 
      dfilterk d k []

    let insert (d : context) (k : var) (v : tp) = 
      let new_dict = delete d k in
      (k, v)::[] @ new_dict
  end

module Ctx = Context

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing ctx e = 
    match e with
    (* Primitive *)
    | Var v ->
    Ctx.lookup ctx v

    | Lam (x, a, e') -> 
    let ctx' = Ctx.insert ctx x a in
    let b = typing ctx' e' in
    Fun (a, b)

    | App (e1, e2) -> 
    let tp1 = typing ctx e1 in
    let tp2 = typing ctx e2 in
    (
        match tp1 with 
        | Fun (a, b) -> 
        if a = tp2
        then b
        else raise TypeError
        | _ -> raise TypeError
    )         

    (* Product *)           
    | Pair (e1, e2) -> 
    let tp1 = typing ctx e1 in
    let tp2 = typing ctx e2 in
    Prod (tp1, tp2)

    | Fst e' -> 
    let tp' = typing ctx e' in
    (
        match tp' with
        | Prod (e1, e2) -> e1
        | _ -> raise TypeError
    )

    | Snd e' -> 
    let tp' = typing ctx e' in
    (
        match tp' with
        | Prod (e1, e2) -> e2
        | _ -> raise TypeError
    )

    | Eunit ->
    Unit 

    (* Sum *)
    | Inl (e1, tp2) -> 
    let tp1 = typing ctx e1 in
    Sum (tp1, tp2)

    | Inr (e1, tp2) -> 
    let tp1 = typing ctx e1 in
    Sum (tp2, tp1)

    | Case (e', x1, e1, x2, e2) ->
    let tp' = typing ctx e' in
    (
        match tp' with
        | Sum (t1, t2) ->
        let ctx1 = Ctx.insert ctx x1 t1 in
        let ctx2 = Ctx.insert ctx x2 t2 in
        let tp = typing ctx1 e1 in
        if tp = typing ctx2 e2
        then tp
        else raise TypeError
        | _ -> raise TypeError
    )

    (* Fixed point combinator *)
    | Fix (x, a, e') ->
    let ctx' = Ctx.insert ctx x a in
    let a' = typing ctx' e' in
    if a = a'
    then a
    else raise TypeError

    (* Boolean *)
    | True ->
    Bool

    | False ->
    Bool

    | Ifthenelse (e', e1, e2) -> 
    let tp' = typing ctx e' in
    (
        match tp' with 
        | Bool ->
        let tp = typing ctx e1 in
        if tp = typing ctx e2
        then tp
        else raise TypeError
        | _ -> raise TypeError
    )

    (* Integer *)
    | Num _ ->
    Int

    | Plus -> 
    Fun (Prod (Int, Int), Int)

    | Minus -> 
    Fun (Prod (Int, Int), Int)

    | Eq -> 
    Fun (Prod (Int, Int), Bool)   



