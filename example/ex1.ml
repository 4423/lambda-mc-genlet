module type S = sig
  type t = int
  val eq: t -> t -> bool
  val ne: t -> t -> bool
end
let f = .<(module struct
  type t = int
  let eq : t -> t -> bool = fun x -> fun y -> int_eq x y
  let ne : t -> t -> bool = fun x -> fun y -> int_ne x y
end : S)>. in f
