module type X__1 = sig type int_t val int : (int -> int_t) val add : (int_t -> (int_t -> int_t)) val sub : (int_t -> (int_t -> int_t)) val mul : (int_t -> (int_t -> int_t)) val div : (int_t -> (int_t -> int_t)) end module type X__2 = sig type int_t val int : (int -> int_t) code val add : (int_t -> (int_t -> int_t)) code val sub : (int_t -> (int_t -> int_t)) code val mul : (int_t -> (int_t -> int_t)) code val div : (int_t -> (int_t -> int_t)) code end module type X__3 = sig type int_t val int : (int -> int_t) code val add : (int_t -> (int_t -> int_t)) code val sub : (int_t -> (int_t -> int_t)) code val mul : (int_t -> (int_t -> int_t)) code val div : (int_t -> (int_t -> int_t)) code end module type X__5 = sig type int_t val int : (int -> int_t) code val add : (int_t -> (int_t -> int_t)) code val sub : (int_t -> (int_t -> int_t)) code val mul : (int_t -> (int_t -> int_t)) code val div : (int_t -> (int_t -> int_t)) code end module type S = X__1
let arith   = (module struct type int_t = int let int   = .<(fun n1 -> n1)>. let add   = .<let int   = (fun n1 -> n1) in (fun n1 -> (fun n2 -> (n1 + n2)))>. let sub   = .<let int   = (fun n1 -> n1) in let add   = (fun n1 -> (fun n2 -> (n1 + n2))) in (fun n1 -> (fun n2 -> (n1 - n2)))>. let mul   = .<let int   = (fun n1 -> n1) in let add   = (fun n1 -> (fun n2 -> (n1 + n2))) in let sub   = (fun n1 -> (fun n2 -> (n1 - n2))) in (fun n1 -> (fun n2 -> (n1 * n2)))>. let div   = .<let int   = (fun n1 -> n1) in let add   = (fun n1 -> (fun n2 -> (n1 + n2))) in let sub   = (fun n1 -> (fun n2 -> (n1 - n2))) in let mul   = (fun n1 -> (fun n2 -> (n1 * n2))) in (fun n1 -> (fun n2 -> (n1 / n2)))>. end : X__2);; let suppressAddZeroOrMulZeroPE   = (fun (m: (module X__5)) -> (module struct module X__4 = (val m) type int_t = (X__4.int_t * bool) let int   = .<(fun n1 -> (if (n1 = 0) then ((.~(X__4.int) 0), true) else ((.~(X__4.int) n1), false)))>. let add   = .<let int   = (fun n1 -> (if (n1 = 0) then ((.~(X__4.int) 0), true) else ((.~(X__4.int) n1), false))) in (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, b1), (n2, b2)) -> (if (b1 && b2) then ((.~(X__4.int) 0), true) else (((.~(X__4.add) n1) n2), false))
))>. let sub   = .<let int   = (fun n1 -> (if (n1 = 0) then ((.~(X__4.int) 0), true) else ((.~(X__4.int) n1), false))) in let add   = (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, b1), (n2, b2)) -> (if (b1 && b2) then ((.~(X__4.int) 0), true) else (((.~(X__4.add) n1) n2), false))
)) in (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, _), (n2, _)) -> (if (n1 = n2) then ((.~(X__4.int) 0), true) else (((.~(X__4.sub) n1) n2), false))
))>. let mul   = .<let int   = (fun n1 -> (if (n1 = 0) then ((.~(X__4.int) 0), true) else ((.~(X__4.int) n1), false))) in let add   = (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, b1), (n2, b2)) -> (if (b1 && b2) then ((.~(X__4.int) 0), true) else (((.~(X__4.add) n1) n2), false))
)) in let sub   = (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, _), (n2, _)) -> (if (n1 = n2) then ((.~(X__4.int) 0), true) else (((.~(X__4.sub) n1) n2), false))
)) in (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, b1), (n2, b2)) -> (if (b1 || b2) then ((.~(X__4.int) 0), true) else (((.~(X__4.mul) n1) n2), false))
))>. let div   = .<let int   = (fun n1 -> (if (n1 = 0) then ((.~(X__4.int) 0), true) else ((.~(X__4.int) n1), false))) in let add   = (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, b1), (n2, b2)) -> (if (b1 && b2) then ((.~(X__4.int) 0), true) else (((.~(X__4.add) n1) n2), false))
)) in let sub   = (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, _), (n2, _)) -> (if (n1 = n2) then ((.~(X__4.int) 0), true) else (((.~(X__4.sub) n1) n2), false))
)) in let mul   = (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, b1), (n2, b2)) -> (if (b1 || b2) then ((.~(X__4.int) 0), true) else (((.~(X__4.mul) n1) n2), false))
)) in (fun n1 -> (fun n2 -> match (n1, n2) with
| ((n1, _), (n2, _)) -> (((.~(X__4.div) n1) n2), false)
))>. end : X__3));; let rec fix  depth m = (if (depth <= 0) then m else ((fix (depth - 1)) (suppressAddZeroOrMulZeroPE m)));; let fix   = ((fix 1000) arith);;
