(*
 * Suzukiらの研究で扱っているFixpoint-Functorの模式的実装 (Recursive Module)
 * Update: 2017-05-27
 *)
let gc = Gc.get ()
let _ = Gc.set { gc with Gc.minor_heap_size = 3200000;
                 space_overhead = max_int }

module type SYM = sig
  type int_t
  type obs_t
  type unit_t
  val int: int -> int_t
  val add: int_t -> int_t -> int_t
  val sub: int_t -> int_t -> int_t
  val mul: int_t -> int_t -> int_t
  val div: int_t -> int_t -> int_t
  val observe: (unit_t -> int_t) -> obs_t
end

module Arith: (SYM with type obs_t = int) = struct
  type int_t = int
  type obs_t = int
  type unit_t = int
  let int = fun n1 -> n1
  let add = fun n1 -> fun n2 -> n1 + n2
  let sub = fun n1 -> fun n2 -> n1 - n2
  let mul = fun n1 -> fun n2 -> n1 * n2
  let div = fun n1 -> fun n2 -> n1 / n2
  let observe = fun f -> f 0
end

module SuppressAddZeroOrMulZeroPE (S: SYM with type obs_t = int)
  : (SYM with type obs_t = int) = struct
  type int_t = S.int_t * bool
  type obs_t = int
  type unit_t = int
  let int = fun n1 -> (S.int n1, n1 = 0)
  let add = fun n1 -> fun n2 ->
    match n1, n2 with
    | (n1, true), (n2, true) ->
      (S.int 0, true)
    | (n1, _), (n2, _) ->
      (S.add n1 n2, false)

  let sub = fun n1 -> fun n2 ->
    match n1, n2 with
      (n1, _), (n2, _) -> if n1 = n2 then (S.int 0, true) else (S.sub n1 n2, false)

  let mul = fun n1 -> fun n2 ->
    match (n1, n2) with
      (n1, b1), (n2, b2) -> if (b1 || b2) then (S.int 0, true) else (S.mul n1 n2, false)

  let div = fun n1 -> fun n2 ->
    match (n1, n2) with
      (n1, _), (n2, _) -> (S.div n1 n2, false)

  let observe = fun f -> 
    match f 0 with
    | (n, _) -> S.observe (fun _ -> n)
end

module rec Fix: (SYM with type obs_t = int) = struct
  module TFix = SuppressAddZeroOrMulZeroPE (Fix)
  module T    = Arith
  type unit_t = int
  type obs_t = int
  type int_t =
    { again: unit_t -> TFix.int_t;
      last: unit_t -> T.int_t }
  let int n0 =
    { again = (fun _ -> TFix.int n0);
      last  = (fun _ -> T.int n0) }
  let add e0 e1 =
    { again = (fun _ -> TFix.add (e0.again 0) (e1.again 0));
      last  = (fun _ -> T.add (e0.last 0) (e1.last 0)) }
  let sub e0 e1 =
    { again = (fun _ -> TFix.sub (e0.again 0) (e1.again 0));
      last  = (fun _ -> T.sub (e0.last 0) (e1.last 0)) }
  let mul e0 e1 =
    { again = (fun _ -> TFix.mul (e0.again 0) (e1.again 0));
      last  = (fun _ -> T.mul (e0.last 0) (e1.last 0)) }
  let div e0 e1 =
    { again = (fun _ -> TFix.div (e0.again 0) (e1.again 0));
      last  = (fun _ -> T.div (e0.last 0) (e1.last 0)) }

  let depth = ref 0
  let limit = int_of_string Sys.argv.(1)
  let rec observe m =
    incr depth;
    let r = if !depth > limit
      then T.observe (fun _ -> (m 0).last 0)
      else TFix.observe (fun _ -> (m 0).again 0) in
    decr depth; r
end
