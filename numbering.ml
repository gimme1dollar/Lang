open Tml
exception NotImplemented 
exception FreeVariable
exception Stuck
exception NotConvertible

type name_context = var list

module type Name_dict =
  sig
    val free_set : texp -> name_context
    val remove_dup : name_context -> name_context
    val lookup : name_context -> var -> int
    val insert : name_context -> var -> name_context 
  end

module Name_context : Name_dict =
  struct
    let rec free_set te = 
      match te with
      | Tvar tx -> [tx]
      | Tlam (tx, ttp, te) ->
        let vars = free_set te in
        List.filter (fun v -> v <> tx) vars
      | Tapp (te1, te2) ->
        (free_set te2) @ (free_set te1)
      | Tpair (te1, te2) -> 
        (free_set te2) @ (free_set te1)
      | Tfst (te) -> 
        free_set te
      | Tsnd (te) -> 
        free_set te
      | Teunit -> []
      | Tinl (te, ttp) -> 
        free_set te
      | Tinr (te, ttp) -> 
        free_set te
      | Tcase (te, tv1, te1, tv2, te2) -> 
        let set0 = free_set te in
        let set1 = List.filter (fun v -> v <> tv1) (free_set te1) in
        let set2 = List.filter (fun v -> v <> tv2) (free_set te2) in
        set2 @ set1 @ set0
      | Tfix (tx, ttp, te) -> 
        let vars = free_set te in
        List.filter (fun v -> v <> tx) vars
      | Ttrue -> []
      | Tfalse -> []
      | Tifthenelse (te, te1, te2) -> 
        (free_set te2) @ (free_set te1) @ (free_set te)
      | Tnum tn -> []
      | Tplus -> []
      | Tminus -> []
      | Teq -> []

    let remove_dup s =
      let unique s x = 
        if List.mem x s 
        then s
        else [x] @ s
      in
      List.rev (List.fold_left unique [] s)

    let lookup (d: name_context) (k: var) = 
      let rec lookup_rec (d: name_context) (k: var) (acc: int) =
        match d with
        | [] -> raise Stuck
        | d_head::[] ->
          if d_head = k
          then acc
          else raise Stuck
        | d_head::d_tails -> 
          if d_head = k
          then acc
          else lookup_rec d_tails k acc+1
      in
      lookup_rec d k 0
      
    let insert (d : name_context) (k : var) = 
      [k] @ d
  end

module Name_ctx = Name_context

let numbering texp = 
  let context = Name_ctx.remove_dup (Name_ctx.free_set texp) in

  let rec numbering' ctx texp =
    match texp with
    | Tvar v ->
      Ind (Name_ctx.lookup ctx v)
    | Tlam (tx, ttp, te) -> 
      let ctx' = Name_ctx.insert ctx tx in
      Lam (numbering' ctx' te)
    | Tapp (te1, te2) -> 
      App (numbering' ctx te1, numbering' ctx te2) 
    | Tpair (te1, te2) -> 
      Pair (numbering' ctx te1, numbering' ctx te2) 
    | Tfst (te) -> Fst (numbering' ctx te)
    | Tsnd (te) -> Snd (numbering' ctx te)
    | Teunit -> Eunit
    | Tinl (te, ttp) -> Inl (numbering' ctx te)
    | Tinr (te, ttp) -> Inr (numbering' ctx te)
    | Tcase (te, tv1, te1, tv2, te2) ->
      let ctx1 = Name_ctx.insert ctx tv1 in
      let ctx2 = Name_ctx.insert ctx tv2 in
      Case (numbering' ctx te, numbering' ctx1 te1, numbering' ctx2 te2) 
    | Tfix (tx, ttp, te) -> 
      let ctx' = Name_ctx.insert ctx tx in
      Fix (numbering' ctx' te)
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (te, te1, te2) -> 
      Ifthenelse (numbering' ctx te, numbering' ctx te1, numbering' ctx te2)
    | Tnum tn -> Num tn
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in

  texp2exp' context texp