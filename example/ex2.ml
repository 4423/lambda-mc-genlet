module type S = sig
  type t
  val fst: t -> t -> t
  val snd: t -> t -> t
end
let f (type a) = fun (module X : S with type t = a) -> .<(module struct
  type t = X.t
  let fst = fun x -> fun y -> X.fst x y
  let snd = fun x -> fun y -> X.snd x y
end : S with type t = a)>.
;;
