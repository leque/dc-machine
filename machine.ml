(**
 An OCaml implementation of a call-by-value abstract machine for lambda-calculus +
   control, shift, control0, shift0, and prompt.
   based on "A dynamic continuation-passing style for dynamic delimited continuations"
   https://dl.acm.org/doi/10.1145/2794078
 *)
type variable = string

type term =
  | Var of variable
  (** variable *)
  | Lam of variable * term
  (** abstraction *)
  | App of term * term
  (** application *)
  | Reset of term
  (** reset (prompt) *)
  | Control of variable * term
  (** control *)
  | Shift of variable * term
  (** shift *)
  | Control0 of variable * term
  (** control0 *)
  | Shift0 of variable * term
  (** shift0 *)

module EnvMap = Map.Make(String)

let (.%[]) env key = EnvMap.find key env

let (.%[]<-) env key v = EnvMap.add key v env

type env = value EnvMap.t
(** mapping from variable to value *)
and value =
  | Closure of variable * term * env
  (** function closure *)
  | ContC of context * trail
  (** continuation captured by control, control0 *)
  | ContS of context * trail
  (** continuation captured by shift, shift0 *)
and context =
  | End
  (** [\[\]] *)
  | Arg of (term * env) * context
  (** [\[\] term] *)
  | Fun of value * context
  (** [value \[\]] *)
and trail = context list
and meta_context = (context * trail) list

(** machine state *)
type state =
  | Eval of term * env * context * trail * meta_context
  (** term evaluation *)
  | Cont1 of context * value * trail * meta_context
  (** context application *)
  | Trail1 of trail * value * meta_context
  (** trail application *)
  | Cont2 of meta_context * value
  (** meta_context application *)

type step =
  | Finish of value
  | Next of state

(** create initial state *)
let init term = Eval (term, EnvMap.empty, End, [], [])

(** one-step reduction *)
let step1 = function
  (* -- Eval transition -- *)
  | Eval (Var x, env, c1, t1, c2) ->
    Next (Cont1 (c1, env.%[x], t1, c2))
  | Eval (Lam (x, e), env, c1, t1, c2) ->
    Next (Cont1 (c1, Closure (x, e, env), t1, c2))
  | Eval (App (e0, e1), env, c1, t1, c2) ->
    Next (Eval (e0, env, Arg ((e1, env), c1), t1, c2))
  | Eval (Reset e, env, c1, t1, c2) ->
    Next (Eval (e, env, End, [], (c1, t1) :: c2))
  | Eval (Control (x, e), env, c1, t1, c2) ->
    Next (Eval (e, (env.%[x] <- ContC (c1, t1)), End, [], c2))
  | Eval (Shift (x, e), env, c1, t1, c2) ->
    Next (Eval (e, (env.%[x] <- ContS (c1, t1)), End, [], c2))
  | Eval (Control0 (x, e), env, c1, t1, (c1', t1') :: c2) ->
    Next (Eval (e, (env.%[x] <- ContC (c1, t1)), c1', t1', c2))
  | Eval (Control0 (x, e), env, c1, t1, []) ->
    Next (Eval (e, (env.%[x] <- ContC (c1, t1)), End, [], []))
  | Eval (Shift0 (x, e), env, c1, t1, (c1', t1') :: c2) ->
    Next (Eval (e, (env.%[x] <- ContS (c1, t1)), c1', t1', c2))
  | Eval (Shift0 (x, e), env, c1, t1, []) ->
    Next (Eval (e, (env.%[x] <- ContS (c1, t1)), End, [], []))
  (* -- Cont1 transition -- *)
  | Cont1 (End, v, t1, c2) ->
    Next (Trail1 (t1, v, c2))
  | Cont1 (Arg ((e, env), c1), v, t1, c2) ->
    Next (Eval (e, env, Fun (v, c1), t1, c2))
  | Cont1 (Fun (Closure (x, e, env), c1), v, t1, c2) ->
    Next (Eval (e, (env.%[x] <- v), c1, t1, c2))
  | Cont1 (Fun (ContC (c1', t1'), c1), v, t1, c2) ->
    Next (Cont1 (c1', v, t1' @ (c1 :: t1), c2))
  | Cont1 (Fun (ContS (c1', t1'), c1), v, t1, c2) ->
    Next (Cont1 (c1', v, t1, (c1', t1') :: c2))
  (* -- Trail1 transition -- *)
  | Trail1 ([], v, c2) ->
    Next (Cont2 (c2, v))
  | Trail1 (c1 :: t1, v, c2) ->
    Next (Cont1 (c1, v, t1, c2))
  (* -- Cont2 transition -- *)
  | Cont2 ((c1, t1) :: c2, v) ->
    Next (Cont1 (c1, v, t1, c2))
  | Cont2 ([], v) ->
    Finish v

(** evaluation *)
let eval term =
  let rec loop = function
    | Finish v -> v
    | Next s -> loop (step1 s)
  in loop @@ Next (init term)
