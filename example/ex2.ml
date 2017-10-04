module type S = sig
  type t
  val fst: t -> t -> t
  val snd: t -> t -> t
end
let f (type a) = fun (m : (module S with type t = a) code) -> .<(module struct
  type t = $m.t
  let fst = fun x -> fun y -> .~($m.fst) x y
  let snd = fun x -> fun y -> .~($m.snd) x y
end : S with type t = a)>.
;;
