module type X__1 = sig 
  type t
  val fst : (t -> (t -> t))
  val snd : (t -> (t -> t))
end
module type X__2 = sig
  type t
  val fst : (t -> (t -> t)) code 
  val snd : (t -> (t -> t)) code
end
module type X__3 = sig
  type t 
  val fst : (t -> (t -> t))
  val snd : (t -> (t -> t))
end
module type S = X__1

let f (type a) = (fun (module X : X__3 with type t = a) ->
  (module struct
    type t = X.t
    let fst = .<(fun x -> (fun y -> ((X.fst x) y)))>.
    let snd = .<let fst = (fun x -> (fun y -> ((X.fst x) y))) in
                (fun x -> (fun y -> ((X.snd x) y)))>.
end : X__2 with type t = a))
;;
