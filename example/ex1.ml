module type S = sig
  type t = int
  val f: t -> t -> t
  val s: t -> t -> t
end
let m = .<(module struct
  type t = int
  let f = fun x -> fun y -> x
  let s = fun x -> fun y -> y
end : S)>.
;;
