let gc = Gc.get ()
let _  = Gc.set { gc with Gc.minor_heap_size = 3200000;
                  space_overhead = max_int }

let bench f =
  let t = Sys.time () in
  ignore (f ()); Printf.printf "%f\n" (Sys.time () -. t)

let rec sequence n acc =
  if (n >= 0) then 
    sequence (n-1) (n::acc) 
  else
    acc

let sequence n = sequence n []

open Set_functor

let _ =
  let n = int_of_string @@ Sys.argv.(1) in
  bench (fun () -> IntSet.member n (sequence n))
