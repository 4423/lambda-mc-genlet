module type EQ = sig
  type t
  val eq: t -> t -> bool
end
module type S = sig
  type elt
  type set
  val member: elt -> set -> bool
end

module MakeSet (Eq: EQ) = struct
  type elt_t = Eq.t
  type set_t = Eq.t list
  let rec member elt set =
    match set with
    | [] -> false
    | elt' :: set' -> Eq.eq elt elt' || member elt set'
end

module IntEq = struct
  type t = int
  let eq = fun x -> fun y -> x = y
end
module IntSet = MakeSet (IntEq)

