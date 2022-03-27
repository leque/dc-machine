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
(** head part of a continuation *)
and trail = context list
  (** trail part of a continuation. head + trail part can be captured by control, etc. *)
and meta_context = (context * trail) list
  (** meta continuation *)

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
  | Eval (Var x, env, c, t, mc) ->
    Next (Cont1 (c, env.%[x], t, mc))
  | Eval (Lam (x, e), env, c, t, mc) ->
    Next (Cont1 (c, Closure (x, e, env), t, mc))
  | Eval (App (e0, e1), env, c, t, mc) ->
    Next (Eval (e0, env, Arg ((e1, env), c), t, mc))
  | Eval (Reset e, env, c, t, mc) ->
    Next (Eval (e, env, End, [], (c, t) :: mc))
  | Eval (Control (x, e), env, c, t, mc) ->
    Next (Eval (e, (env.%[x] <- ContC (c, t)), End, [], mc))
  | Eval (Shift (x, e), env, c, t, mc) ->
    Next (Eval (e, (env.%[x] <- ContS (c, t)), End, [], mc))
  | Eval (Control0 (x, e), env, c, t, (c', t') :: mc) ->
    Next (Eval (e, (env.%[x] <- ContC (c, t)), c', t', mc))
  | Eval (Control0 (x, e), env, c, t, []) ->
    Next (Eval (e, (env.%[x] <- ContC (c, t)), End, [], []))
  | Eval (Shift0 (x, e), env, c, t, (c', t') :: mc) ->
    Next (Eval (e, (env.%[x] <- ContS (c, t)), c', t', mc))
  | Eval (Shift0 (x, e), env, c, t, []) ->
    Next (Eval (e, (env.%[x] <- ContS (c, t)), End, [], []))
  (* -- Cont1 transition -- *)
  | Cont1 (End, v, t, mc) ->
    Next (Trail1 (t, v, mc))
  | Cont1 (Arg ((e, env), c), v, t, mc) ->
    Next (Eval (e, env, Fun (v, c), t, mc))
  | Cont1 (Fun (Closure (x, e, env), c), v, t, mc) ->
    Next (Eval (e, (env.%[x] <- v), c, t, mc))
  | Cont1 (Fun (ContC (c', t'), c), v, t, mc) ->
    Next (Cont1 (c', v, t' @ (c :: t), mc))
  | Cont1 (Fun (ContS (c', t'), c), v, t, mc) ->
    Next (Cont1 (c', v, t', (c, t) :: mc))
  (* -- Trail1 transition -- *)
  | Trail1 ([], v, mc) ->
    Next (Cont2 (mc, v))
  | Trail1 (c :: t, v, mc) ->
    Next (Cont1 (c, v, t, mc))
  (* -- Cont2 transition -- *)
  | Cont2 ((c, t) :: mc, v) ->
    Next (Cont1 (c, v, t, mc))
  | Cont2 ([], v) ->
    Finish v

(** evaluation *)
let eval term =
  let rec loop = function
    | Finish v -> v
    | Next s -> loop (step1 s)
  in loop @@ Next (init term)
