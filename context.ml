open Tml
exception NotImplemented 
exception FreeVariable
exception Stuck
exception NotConvertible

type stoval = 
  | Computed of value 
  | Delayed of exp * env

and stack =
  | Hole_SK
  | Frame_SK of stack * frame

and state =
  | Anal_ST of (stoval Heap.heap) * stack * exp * env
  | Return_ST of (stoval Heap.heap) * stack * value

and env = (exp * Heap.loc) list

and value =
  | Lam_VL of exp * env
  | Pair_VL of exp * env
  | Unit_VL
  | Inl_VL of exp * env
  | Inr_VL of exp * env
  | True_VL
  | False_VL 
  | Num_VL of exp
  | Plus_VL 
  | Minus_VL
  | Eq_VL

and frame = 
  | Delayed_val of (Heap.loc) (* will be val in env heap *)
  | App_FR of (env * exp)
  | Fst_FR of (env)
  | Snd_FR of (env)
  | Case_FR of (env * exp * exp)
  | Ifthenelse_FR of (env * exp * exp)
  | Plus_FR of (env)
  | Plus_e1_hole_FR of (env * exp)
  | Plus_hole_value_FR of (env * value)
  | Minus_FR of (env)
  | Minus_e1_hole_FR of (env * exp)
  | Minus_hole_value_FR of (env * value)
  | Eq_FR of (env)
  | Eq_e1_hole_FR of (env * exp)
  | Eq_hole_value_FR of (env * value)


module type Env_dict =
  sig
    val empty : unit -> env
    val lookup : env -> exp -> Heap.loc
    val insert : env -> exp -> Heap.loc -> env 
  end

module Env_context : Env_dict =
  struct
    let empty () = []

    let rec lookup (d: env) (e: exp) = 
      match e with
      | Ind i ->
        (
          match d with
          | [] -> raise Stuck
          | (d_head_ind, d_head_loc)::[] ->
            (
              match d_head_ind with
              | Ind hi -> 
                if hi = i
                then d_head_loc
                else raise Stuck
              | _ -> raise Stuck
            )
          | (d_head_ind, d_head_loc)::d_tails -> 
            (
              match d_head_ind with
              | Ind hi -> 
                if hi = i
                then d_head_loc
                else lookup d_tails e
              | _ -> raise Stuck
            )
        )
      | _ -> raise Stuck
      
    let insert (d : env) (e : exp) (l : Heap.loc) = 
      let rec update_dict (d' : env) =
        match d' with
        | [] -> []
        | (d_head_ind, d_head_loc)::[] -> 
          (
          match d_head_ind with
          | Ind hi ->
            [(Ind (hi + 1), d_head_loc)]
          | _ -> raise Stuck
          )
        | (d_head_ind, d_head_loc)::d_tails ->
          (
          match d_head_ind with
          | Ind hi ->
            [(Ind (hi + 1), d_head_loc)] @ (update_dict d_tails)
          | _ -> raise Stuck
          ) 
      in
      
      let ud = update_dict d in

      match e with
      | Ind i -> ud @ [(Ind i, l)]
      | _ -> raise Stuck
  end

module Env_ctx = Env_context

let emptyEnv = Env_ctx.empty ()

let value2exp v =
  match v with
  | Lam_VL _ -> raise NotConvertible
  | Pair_VL _ -> raise NotConvertible
  | Unit_VL -> Eunit
  | Inl_VL _ -> raise NotConvertible
  | Inr_VL _ -> raise NotConvertible
  | True_VL -> True
  | False_VL -> False
  | Num_VL n -> n
  | Plus_VL -> raise NotConvertible
  | Minus_VL -> raise NotConvertible
  | Eq_VL -> raise NotConvertible

let reduce s = 
  let concat_stack s f = 
    Frame_SK (s, f)
  in

  match s with
  | Anal_ST (heap, stack, exp, env) -> 
    (
      match exp with
      | Ind i -> 
        (
          let loc = Env_ctx.lookup env exp in
          let value = Heap.deref heap loc in
          (
            match value with
            | Delayed (exp', env') ->
              let frame' = Delayed_val loc in
              let stack' = concat_stack stack frame' in
              Anal_ST (heap, stack', exp', env')
            | Computed value' ->
              Return_ST (heap, stack, value')
          )
        )
      | Lam e -> 
        let closed_value = Lam_VL (Lam e, env) in
        Return_ST (heap, stack, closed_value)
      | App (e1, e2) -> 
        let frame' = App_FR (env, e2) in
        let stack' = concat_stack stack frame' in
        Anal_ST (heap, stack', e1, env)
      | Pair (e1, e2) -> 
        let closed_value = Pair_VL (Pair (e1, e2), env) in
        Return_ST (heap, stack, closed_value)
      | Fst e -> 
        let frame' = Fst_FR (env) in
        let stack' = concat_stack stack frame' in
        Anal_ST (heap, stack', e, env)
      | Snd e -> 
        let frame' = Snd_FR (env) in
        let stack' = concat_stack stack frame' in
        Anal_ST (heap, stack', e, env)
      | Eunit -> 
        Return_ST (heap, stack, Unit_VL)
      | Inl e -> 
        let closed_value = Inl_VL (e, env) in
        Return_ST (heap, stack, closed_value)
      | Inr e -> 
        let closed_value = Inr_VL (e, env) in
        Return_ST (heap, stack, closed_value)
      | Case (e, e1, e2) -> 
        let frame' = Case_FR (env, e1, e2) in
        let stack' = concat_stack stack frame' in
        Anal_ST (heap, stack', e, env)
      | True -> 
        Return_ST (heap, stack, True_VL)
      | False -> 
        Return_ST (heap, stack, False_VL)
      | Ifthenelse (e, e1, e2) -> 
        let frame' = Ifthenelse_FR (env, e1, e2) in
        let stack' = concat_stack stack frame' in
        Anal_ST (heap, stack', e, env)
      | Fix e -> 
        let allocating_val = Delayed (Fix e, env) in
        let (heap_alloc, loc) = Heap.allocate heap allocating_val in
        let env' = Env_ctx.insert env (Ind 0) loc in 
        Anal_ST (heap_alloc, stack, e, env')
      | Num n -> 
        Return_ST (heap, stack, Num_VL (Num n))   
      | Plus -> 
        Return_ST (heap, stack, Plus_VL)
      | Minus -> 
        Return_ST (heap, stack, Minus_VL)
      | Eq -> 
        Return_ST (heap, stack, Eq_VL)
    )
  | Return_ST (heap, stack, value) -> 
    (
      match stack with
      | Hole_SK -> raise Stuck
      | Frame_SK (stack', fr) ->
        (
          match fr with
          | Delayed_val l -> 
            let computed_val = Computed value in 
            let heap_update = Heap.update heap l computed_val in
            Return_ST (heap_update, stack', value)
          | App_FR (stoenv, e2) ->
            (
              match value with
              | Lam_VL (Lam e, lamenv) ->
                let allocating_val = Delayed (e2, stoenv) in
                let (heap_alloc, loc) = Heap.allocate heap allocating_val in
                let env' = Env_ctx.insert lamenv (Ind 0) loc in (* Bound to 0, lamenv get upated during insertion*)
                Anal_ST (heap_alloc, stack', e, env')
              | Plus_VL ->
                let frame' = Plus_FR (stoenv) in
                let stack' = concat_stack stack' frame' in
                Anal_ST (heap, stack', e2, stoenv)
              | Minus_VL ->
                let frame' = Minus_FR (stoenv) in
                let stack' = concat_stack stack' frame' in
                Anal_ST (heap, stack', e2, stoenv)
              | Eq_VL ->
                let frame' = Eq_FR (stoenv) in
                let stack' = concat_stack stack' frame' in
                Anal_ST (heap, stack', e2, stoenv)
              | _ -> raise Stuck
            )
          | Fst_FR (stoenv) ->
            (
              match value with
              | Pair_VL (Pair (e1, e2), env) ->
                Anal_ST (heap, stack', e1, env)
              | _ -> raise Stuck
            )
          | Snd_FR (stoenv) ->
            (
              match value with
              | Pair_VL (Pair (e1, e2), env) ->
                Anal_ST (heap, stack', e2, env)
              | _ -> raise Stuck
            )
          | Case_FR (stoenv, e1, e2) ->
            (
              match value with
              | Inl_VL (e', inlenv) ->
                let allocating_val = Delayed (e', inlenv) in
                let (heap_alloc, loc) = Heap.allocate heap allocating_val in
                let env = Env_ctx.insert stoenv (Ind 0) loc in (* Bound to 0, inlenv get upated during insertion*)
                Anal_ST (heap_alloc, stack', e1, env)
              | Inr_VL (e', inrenv) -> 
                let allocating_val = Delayed (e', inrenv) in
                let (heap_alloc, loc) = Heap.allocate heap allocating_val in
                let env = Env_ctx.insert stoenv (Ind 0) loc in (* Bound to 0, inlenv get upated during insertion*)
                Anal_ST (heap_alloc, stack', e2, env)
              | _ -> raise Stuck
            )
          | Ifthenelse_FR (stoenv, e1, e2) ->
            (
              match value with
              | True_VL ->
                Anal_ST (heap, stack', e1, stoenv)
              | False_VL -> 
                Anal_ST (heap, stack', e2, stoenv)
              | _ -> raise Stuck
            )
          | Plus_FR (stoenv) ->
            (
              match value with
              | Pair_VL (Pair (e1, e2), env) ->
                let stack'' = concat_stack stack' (Plus_e1_hole_FR (env, e2)) in
                Anal_ST (heap, stack'', e1, env)
              | _ -> raise Stuck
            )
          | Plus_e1_hole_FR (stoenv, stoexp) ->
            (
              match value with
              | Num_VL (Num m) ->
                let stack'' = concat_stack stack' (Plus_hole_value_FR (stoenv, (Num_VL (Num m)))) in
                Anal_ST (heap, stack'', stoexp, stoenv)
              | _ -> raise Stuck
            )
          | Plus_hole_value_FR (stoenv, stonum) ->
            (
              match value with
              | Num_VL (Num n) ->
                (
                  match stonum with
                  | Num_VL (Num m) -> 
                    Anal_ST (heap, stack', Num (n+m), stoenv)
                  | _ -> raise Stuck
                )
              | _ -> raise Stuck
            )
          | Minus_FR (stoenv) -> 
            (
              match value with
              | Pair_VL (Pair (e1, e2), env) ->
                let stack'' = concat_stack stack' (Minus_e1_hole_FR (env, e2)) in
                Anal_ST (heap, stack'', e1, env)
              | _ -> raise Stuck
            )
          | Minus_e1_hole_FR (stoenv, stoexp) -> 
            (
              match value with
              | Num_VL (Num m) ->
                let stack'' = concat_stack stack' (Minus_hole_value_FR (stoenv, (Num_VL (Num m)))) in
                Anal_ST (heap, stack'', stoexp, stoenv)
              | _ -> raise Stuck
            )
          | Minus_hole_value_FR (stoenv, stonum) -> 
            (
              match value with
              | Num_VL (Num n) ->
                (
                  match stonum with
                  | Num_VL (Num m) -> 
                    Anal_ST (heap, stack', Num (m-n), stoenv)
                  | _ -> raise Stuck
                )
              | _ -> raise Stuck
            )
          | Eq_FR (stoenv) -> 
            (
              match value with
              | Pair_VL (Pair (e1, e2), env) ->
                let stack'' = concat_stack stack' (Eq_e1_hole_FR (env, e2)) in
                Anal_ST (heap, stack'', e1, env)
              | _ -> raise Stuck
            )
          | Eq_e1_hole_FR (stoenv, stoexp) -> 
            (
              match value with
              | Num_VL (Num m) ->
                let stack'' = concat_stack stack' (Eq_hole_value_FR (stoenv, (Num_VL (Num m)))) in
                Anal_ST (heap, stack'', stoexp, stoenv)
              | _ -> raise Stuck
            )
          | Eq_hole_value_FR (stoenv, stonum) -> 
            (
              match value with
              | Num_VL (Num n) ->
                (
                  match stonum with
                  | Num_VL (Num m) -> 
                    if n = m
                    then Anal_ST (heap, stack', True, stoenv)
                    else Anal_ST (heap, stack', False, stoenv)
                  | _ -> raise Stuck
                )
              | _ -> raise Stuck
            )
        )
      )
