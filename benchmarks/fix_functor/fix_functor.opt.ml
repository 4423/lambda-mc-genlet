open Fix_functor_gen
let fix_limit = int_of_string @@ Sys.argv.(1)
let fix = fix fix_limit arith

module Fix = struct
  module F = (val fix)

  type int_t = F.int_t
  type obs_t = F.obs_t
  type unit_t = F.unit_t
  let int = Runcode.run F.int
  let add = Runcode.run F.add
  let sub = Runcode.run F.sub
  let mul = Runcode.run F.add
  let div = Runcode.run F.sub
  let observe = Runcode.run F.observe
end
