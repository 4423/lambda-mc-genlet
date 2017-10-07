module type S = sig
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

let arith = .<(module struct
  type int_t = int
  type obs_t = int
  type unit_t = int
  let int = fun n1 -> n1
  let add = fun n1 -> fun n2 -> n1 + n2
  let sub = fun n1 -> fun n2 -> n1 - n2
  let mul = fun n1 -> fun n2 -> n1 * n2
  let div = fun n1 -> fun n2 -> n1 / n2
  let observe = fun f -> f 0
end: S with type obs_t = int)>.
;;

let suppressAddZeroOrMulZeroPE = fun (m: (module S with type obs_t = int) code) ->
  .<(module struct
      type int_t = $m.int_t * bool
      type obs_t = int
      type unit_t = int
      let int = fun n1 -> if n1 = 0 then (.~($m.int) 0, true) else (.~($m.int) n1, false)
      let add = fun n1 -> fun n2 -> 
        match (n1, n2) with
          (n1, b1), (n2, b2) -> if (b1 && b2) then (.~($m.int) 0, true) else .~($m.add) n1 n2
      let sub = fun n1 -> fun n2 ->
        if n1 = n2 then (.~($m.int) 0, true) else .~($m.sub) n1 n2
      let mul = fun n1 -> fun n2 ->
        match (n1, n2) with
          (n1, b1), (n2, b2) -> if (b1 || b2) then (.~($m.int) 0, true) else .~($m.mul) n1 n2
      let div = fun n1 -> fun n2 ->
        match (n1, n2) with
          (n1, _), (n2, _) -> .~($m.div) n1 n2, false
      let observe = fun f ->
        match f 0 with
          (n, _) -> .~($m.observe) (fun _ -> n)
    end: S with type obs_t = int)>.
;;
let rec fix depth m =
  if depth <= 0 then
    m
  else
    fix (depth - 1) (suppressAddZeroOrMulZeroPE m)
;;
