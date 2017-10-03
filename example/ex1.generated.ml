module type X__1 = sig
  type t = int
  val f : (t -> (t -> t))
  val s : (t -> (t -> t))
end 
module type X__2 = sig 
  type t = int
  val f : (t -> (t -> t)) code
  val s : (t -> (t -> t)) code
end

module type S = X__1

let m = (module struct
  type t = int
  let f = .<(fun x -> (fun y -> x))>.
  let s = .<let f = (fun x -> (fun y -> x)) in
            (fun x -> (fun y -> y))>.
 end : X__2)
;;
