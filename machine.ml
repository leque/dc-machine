type variable = string

type term =
  | Var of variable
  | Lam of variable * term
  | App of term * term
  | Reset of term
  | Control of variable * term

module EnvMap = Map.Make(String)

type env = value EnvMap.t
and value =
  | Closure of variable * term * env
  | Cont of context * trail
and context =
  | End
  | Arg of (term * env) * context
  | Fun of value * context
and trail = context list
and meta_context = (context * trail) list

type state =
  | Eval of term * env * context * trail * meta_context
  | Cont1 of context * value * trail * meta_context
  | Trail1 of trail * value * meta_context
  | Cont2 of meta_context * value

let init term = Eval (term, EnvMap.empty, End, [], [])

type step = Finish of value | Next of state

let step1 = function
  | Eval (Var x, env, c1, t1, c2) ->
    Next (Cont1 (c1, EnvMap.find x env, t1, c2))
  | Eval (Lam (x, e), env, c1, t1, c2) ->
    Next (Cont1 (c1, Closure (x, e, env), t1, c2))
  | Eval (App (e0, e1), env, c1, t1, c2) ->
    Next (Eval (e0, env, Arg ((e1, env), c1), t1, c2))
  | Eval (Reset e, env, c1, t1, c2) ->
    Next (Eval (e, env, End, [], (c1, t1) :: c2))
  | Eval (Control (x, e), env, c1, t1, c2) ->
    Next (Eval (e, EnvMap.add x (Cont (c1, t1)) env, End, [], c2))
  | Cont1 (End, v, t1, c2) ->
    Next (Trail1 (t1, v, c2))
  | Cont1 (Arg ((e, env), c1), v, t1, c2) ->
    Next (Eval (e, env, Fun (v, c1), t1, c2))
  | Cont1 (Fun (Closure (x, e, env), c1), v, t1, c2) ->
    Next (Eval (e, EnvMap.add x v env, c1, t1, c2))
  | Cont1 (Fun (Cont (c1', t1'), c1), v, t1, c2) ->
    Next (Cont1 (c1', v, t1' @ (c1 :: t1), c2))
  | Trail1 ([], v, c2) ->
    Next (Cont2 (c2, v))
  | Trail1 (c1 :: t1, v, c2) ->
    Next (Cont1 (c1, v, t1, c2))
  | Cont2 ((c1, t1) :: c2, v) ->
    Next (Cont1 (c1, v, t1, c2))
  | Cont2 ([], v) ->
    Finish v

let eval term =
  let rec loop = function
    | Finish v -> v
    | Next s -> loop (step1 s)
  in loop @@ Next (init term)
