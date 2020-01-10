(*
 * Copyright (c) 2017 Takahisa Watanabe <takahisa@logic.cs.tsukuba.ac.jp> All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *)
open Norm

let insert_genlet e = E0.(AppE (VarE "genlet", e))

let rec f : (E.mod_decl list * E.toplevel list) -> (E.mod_decl list * E.toplevel list) =
  fun (decl_list, toplevel_list) ->
    let decl_list' = List.map begin function
      | E.StructureDec (x0, m0) -> E.StructureDec (x0, structure0 [] [] m0)
      | E.SignatureDec (x0, s0) -> E.SignatureDec (x0, signature0 [] s0)
    end decl_list in
    let toplevel_list' = List.map begin function
      | E.Toplevel_Let (x0, xs0, ys0, e0)     -> E.Toplevel_Let (x0, xs0, ys0, term0 [] [] e0)
      | E.Toplevel_LetRec (x0, xs0, ys0, e0)  -> E.Toplevel_LetRec (x0, xs0, ys0, term0 [] [] e0)
    end toplevel_list in
    decl_list', toplevel_list'

and term0 env d = function
  | E0.VarE x0                        -> E0.VarE x0
  | E0.AccE (E0.VarP x0, x1)          -> E0.(AccE (VarP x0, x1))
  | E0.AccE (E0.DollarP x0, x1)       -> E0.(AccE (VarP (List.assoc x0 env), x1)) 
  | E0.IntE n0                        -> E0.IntE n0
  | E0.BoolE b0                       -> E0.BoolE b0
  | E0.LetE (x0, xs0, ys0, e0, e1)    -> E0.LetE (x0, xs0, ys0, term0 env d e0, term0 env d e1)
  | E0.LetRecE (x0, xs0, ys0, e0, e1) -> E0.LetRecE (x0, xs0, ys0, term0 env d e0, term0 env d e1)
  | E0.LetModE (x0, m0, e0)           -> E0.LetModE (x0, structure0 env d m0, term0 env d e0)
  | E0.FunE (x0, Some t0, e0)         -> E0.FunE (x0, Some (type0 env t0), term0 env d e0)
  | E0.FunE (x0, None, e0)            -> E0.FunE (x0, None, term0 env d e0)
  | E0.FunModE (x0, s0, e0)           -> E0.FunModE (x0, signature0 env s0, term0 env d e0)
  | E0.AppE (e0, e1)                  -> E0.AppE (term0 env d e0, term0 env d e1)
  | E0.IfE (e0, e1, e2)               -> E0.IfE (term0 env d e0, term0 env d e1, term0 env d e2)
  | E0.NegE e0                        -> E0.NegE (term0 env d e0)
  | E0.NotE e0                        -> E0.NotE (term0 env d e0)
  | E0.AddE (e0, e1)                  -> E0.AddE (term0 env d e0, term0 env d e1)
  | E0.SubE (e0, e1)                  -> E0.SubE (term0 env d e0, term0 env d e1)
  | E0.MulE (e0, e1)                  -> E0.MulE (term0 env d e0, term0 env d e1)
  | E0.DivE (e0, e1)                  -> E0.DivE (term0 env d e0, term0 env d e1)
  | E0.EqE (e0, e1)                   -> E0.EqE (term0 env d e0, term0 env d e1)
  | E0.NeE (e0, e1)                   -> E0.NeE (term0 env d e0, term0 env d e1)
  | E0.GtE (e0, e1)                   -> E0.GtE (term0 env d e0, term0 env d e1)
  | E0.LeE (e0, e1)                   -> E0.LeE (term0 env d e0, term0 env d e1)
  | E0.GtEqE (e0, e1)                 -> E0.GtEqE (term0 env d e0, term0 env d e1)
  | E0.LeEqE (e0, e1)                 -> E0.LeEqE (term0 env d e0, term0 env d e1)
  | E0.DisjE (e0, e1)                 -> E0.DisjE (term0 env d e0, term0 env d e1)
  | E0.ConjE (e0, e1)                 -> E0.ConjE (term0 env d e0, term0 env d e1)
  | E0.ConsE (e0, e1)                 -> E0.ConsE (term0 env d e0, term0 env d e1)
  | E0.PairE (e0, e1)                 -> E0.PairE (term0 env d e0, term0 env d e1)
  | E0.CodE e0                        -> E0.CodE (term1 env d e0)
  | E0.RunE e0                        -> E0.RunE (term0 env d e0)
  | E0.ModE (m0, s0)                  -> E0.ModE (structure0 env d m0, signature0 env s0)
  | E0.ModCodE (m0, s0)               -> E0.ModE (structure1 env d m0, signature1 env s0)
  | E0.RunModE (e0, s0)               -> runmod_e env d e0 s0
  | E0.MatchE (e0, cs0)               -> E0.MatchE (term0 env d e0, List.map begin
                                           fun (pattern, body) -> (pattern, term0 env d body)
                                         end cs0)

and runmod_e env d e s =
  let name = Fresh.con () in
  let unpacked_mods = E0.(ModM (name, UnpackM (term0 env d e))) in
  let cs = runmod_structure name s in
  E0.(ModE (Structure (unpacked_mods :: cs), signature0 env s))
and runmod_structure mod_name = function
  | E.Signature cs0       -> List.map (runmod_structure_component mod_name) cs0
  | E.Sharing (s0, _, _)  -> runmod_structure mod_name s0
and runmod_structure_component mod_name = function
  | E.TypeS (x0, _) -> E0.TypeM (x0, Some E.(AccT (VarP mod_name, x0)))
  | E.ValS (x0, _)  -> E0.LetM (x0, [], [], E0.(RunE (AccE (VarP mod_name, x0))))
  | E.ModS (x0, s0) -> let e = E0.(ModE (VarM (mod_name^"."^x0), s0)) in
                       E0.(ModM (x0, UnpackM (runmod_e [] [] e s0)))

and term1 env d = function
  | E1.VarE x0                        -> if List.mem x0 d then E1.(EscE (VarE x0))
                                         else E1.VarE x0
  | E1.AccE (E1.VarP x0, x1)          -> if List.mem x0 d then E1.EscE E0.(AccE (VarP x0, x1))
                                         else E1.(AccE (VarP x0, x1))
  | E1.IntE n0                        -> E1.IntE n0
  | E1.BoolE b0                       -> E1.BoolE b0
  | E1.LetE (x0, xs0, ys0, e0, e1)    -> E1.LetE (x0, xs0, ys0, term1 env d e0, term1 env d e1)
  | E1.LetRecE (x0, xs0, ys0, e0, e1) -> E1.LetRecE (x0, xs0, ys0, term1 env d e0, term1 env d e1)
  | E1.FunE (x0, Some t0, e0)         -> E1.FunE (x0, Some (type1 env t0), term1 env d e0)
  | E1.FunE (x0, None, e0)            -> E1.FunE (x0, None, term1 env d e0)
  | E1.AppE (e0, e1)                  -> E1.AppE (term1 env d e0, term1 env d e1)
  | E1.IfE (e0, e1, e2)               -> E1.IfE (term1 env d e0, term1 env d e1, term1 env d e2)
  | E1.NegE e0                        -> E1.NegE (term1 env d e0)
  | E1.NotE e0                        -> E1.NotE (term1 env d e0)
  | E1.AddE (e0, e1)                  -> E1.AddE (term1 env d e0, term1 env d e1)
  | E1.SubE (e0, e1)                  -> E1.SubE (term1 env d e0, term1 env d e1)
  | E1.MulE (e0, e1)                  -> E1.MulE (term1 env d e0, term1 env d e1)
  | E1.DivE (e0, e1)                  -> E1.DivE (term1 env d e0, term1 env d e1)
  | E1.EqE (e0, e1)                   -> E1.EqE (term1 env d e0, term1 env d e1)
  | E1.NeE (e0, e1)                   -> E1.NeE (term1 env d e0, term1 env d e1)
  | E1.GtE (e0, e1)                   -> E1.GtE (term1 env d e0, term1 env d e1)
  | E1.LeE (e0, e1)                   -> E1.LeE (term1 env d e0, term1 env d e1)
  | E1.GtEqE (e0, e1)                 -> E1.GtEqE (term1 env d e0, term1 env d e1)
  | E1.LeEqE (e0, e1)                 -> E1.LeEqE (term1 env d e0, term1 env d e1)
  | E1.DisjE (e0, e1)                 -> E1.DisjE (term1 env d e0, term1 env d e1)
  | E1.ConjE (e0, e1)                 -> E1.ConjE (term1 env d e0, term1 env d e1)
  | E1.ConsE (e0, e1)                 -> E1.ConsE (term1 env d e0, term1 env d e1)
  | E1.PairE (e0, e1)                 -> E1.PairE (term1 env d e0, term1 env d e1)
  | E1.EscE e0                        -> E1.EscE (term0 env d e0)
  | E1.ModE _                         -> failwith "[error] ``module`` is not allowed to appear at level-1 term"
  | E1.MatchE (e0, cs0)               -> E1.MatchE (term1 env d e0, List.map begin
                                           fun (pattern, body) -> (pattern, term1 env d body)
                                         end cs0)

and type0 env = function
  | E.VarT x0                 -> E.VarT x0
  | E.AccT (E.VarP x0, x1)    -> E.AccT (E.VarP x0, x1)
  | E.AccT (E.DollarP x0, x1) -> E.AccT (E.VarP (List.assoc x0 env), x1)
  | E.ArrT (t0, t1)           -> E.ArrT (type0 env t0, type0 env t1)
  | E.AppT (t0, t1)           -> E.AppT (type0 env t0, type0 env t1)
  | E.PairT (t0, t1)          -> E.PairT (type0 env t0, type0 env t1)
  | E.CodT t0                 -> E.CodT (type1 env t0)
  | E.ModT s0                 -> E.ModT (signature0 env s0)
  | E.ModCodT s0              -> E.ModT (signature1 env s0)
  | E.EscT _                  -> failwith "[error] ``<esc>`` is not allowed to appear at level-0 type"

and type1 env = function
  | E.VarT x0                 -> E.VarT x0
  | E.AccT (E.VarP x0, x1)    -> E.AccT (E.VarP x0, x1)
  | E.AccT (E.DollarP x0, x1) -> E.AccT (E.VarP (List.assoc x0 env), x1)
  | E.ArrT (t0, t1)           -> E.ArrT (type1 env t0, type1 env t1)
  | E.AppT (t0, t1)           -> E.AppT (type1 env t0, type1 env t1)
  | E.PairT (t0, t1)          -> E.PairT (type1 env t0, type1 env t1)
  | E.CodT _                  -> failwith "[error] ``code`` is not allowed to appear at level-1 type"
  | E.ModT _                  -> failwith "[error] ``mod`` is not allowed to appear at level-1 type"
  | E.ModCodT _               -> failwith "[error] ``code`` is not allowed to appear at level-1 type"
  | E.EscT t0                 -> E.EscT (type0 env t0)

and signature0 env = function
  | E.Signature cs0         -> E.Signature (List.map (signature_component0 env) cs0)
  | E.Sharing (s0, x0, t0)  -> E.Sharing (signature0 env s0, x0, type0 env t0)
and signature_component0 env = function
  | E.TypeS (x0, Some t0)   -> E.TypeS (x0, Some (type0 env t0))
  | E.TypeS (x0, None)      -> E.TypeS (x0, None)
  | E.ValS (x0, t0)         -> E.ValS (x0, type0 env t0)
  | E.ModS (x0, m0)         -> E.ModS (x0, signature0 env m0)

and signature1 env = function
  | E.Signature cs0         -> E.Signature (List.map (signature_component1 env) cs0)
  | E.Sharing (s0, x0, t0)  -> E.Sharing (signature1 env s0, x0, type1 env t0)
and signature_component1 env = function
  | E.TypeS (x0, Some t0)   -> E.TypeS (x0, Some (type1 env t0))
  | E.TypeS (x0, None)      -> E.TypeS (x0, None)
  | E.ValS (x0, t0)         -> E.ValS (x0, E.CodT (type1 env t0))
  | E.ModS (x0, m0)         -> E.ModS (x0, signature1 env m0)

and structure0 env d = function
  | E0.Structure cs0  -> E0.Structure (List.map (structure_component0 env d) cs0)
  | E0.UnpackM e0     -> E0.UnpackM (term0 env d e0)
  | E0.VarM x0        -> E0.VarM x0
and structure_component0 env d = function
  | E0.TypeM (x0, Some t0)        -> E0.TypeM (x0, Some (type0 env t0))
  | E0.TypeM (x0, None)           -> E0.TypeM (x0, None)
  | E0.LetRecM (x0, xs0, ys0, e0) -> E0.LetRecM (x0, xs0, ys0, term0 env d e0)
  | E0.LetM (x0, xs0, ys0, e0)    -> E0.LetM (x0, xs0, ys0, term0 env d e0)
  | E0.ModM (x0, m0)              -> E0.ModM (x0, structure0 env d m0)

and structure1 env d = function
  | E1.Structure cs0  -> 
      let set = dollar_var_set cs0 in
      let (bindings, unpacked_mods) = List.split @@ List.map begin fun var ->
        let con = Fresh.con () in
        ((var, con), E0.(ModM (con, UnpackM (VarE var))))        
      end (Set.elements set) in
      let (_,_, cs0') = List.fold_left structure_component1 (d, bindings @ env, []) cs0 in
      E0.Structure (unpacked_mods @ List.rev cs0')
  | E1.UnpackM (E1.ModE (m0, s0)) -> E0.(UnpackM (ModE (structure1 env d m0, signature1 env s0)))
  | E1.UnpackM _                  -> failwith "[error] only module is only allowed to appear within unpack"
  | E1.VarM x0                    -> E0.VarM x0
and structure_component1 (d, env, cs) = function
  | E1.TypeM (x0, Some t0)        -> (d, env, E0.TypeM (x0, Some (type1 env t0)) :: cs)
  | E1.TypeM (x0, None)           -> (d, env, E0.TypeM (x0, None) :: cs)
  | E1.LetRecM (x0, xs0, ys0, e0) -> let e1 = term1 env d (E1.LetRecE (x0, xs0, ys0, e0, E1.VarE x0)) in
                                     (x0::d, env, E0.LetM (x0, [], [], insert_genlet (E0.CodE e1)) :: cs)
  | E1.LetM (x0, xs0, ys0, e0)    -> (x0::d, env, E0.LetM (x0, xs0, ys0, insert_genlet (E0.CodE (term1 env d e0))) :: cs)
  | E1.ModM (x0, m0)              -> (x0::d, env, E0.ModM (x0, structure1 env d m0) :: cs)


and dollar_var_set components = 
  dollar_structure components
and dollar_structure cs = 
  List.fold_right Set.union (List.map dollar_structure_component cs) Set.empty
and dollar_structure_component = function
  | E1.TypeM (_, Some t0)         -> dollar_core_type t0
  | E1.LetRecM (_, _, _, e0)
  | E1.LetM (_, _, _, e0)         -> dollar_e1 e0
  | E1.ModM (_, E1.Structure cs0) -> dollar_structure cs0
  | E1.ModM (_, E1.UnpackM e0)    -> dollar_e1 e0
  | _                             -> Set.empty
and dollar_core_type = function
  | E.AccT (E.DollarP x0, _)  -> Set.singleton x0
  | E.ArrT (t0, t1) 
  | E.PairT (t0, t1)          -> Set.union (dollar_core_type t0) (dollar_core_type t1)
  | E.CodT t0 
  | E.EscT t0                 -> dollar_core_type t0
  | _                         -> Set.empty
and dollar_e0 = function
  | E0.AccE (E0.DollarP x0, _) 
    -> Set.singleton x0
  | E0.IfE (e0, e1, e2) 
    -> Set.union (dollar_e0 e0) (Set.union (dollar_e0 e1) (dollar_e0 e2))
  | E0.LetE (_, _, _, e0, e1) | E0.LetRecE (_, _, _, e0, e1) | E0.AppE (e0, e1)
  | E0.AddE (e0, e1) | E0.SubE (e0, e1) | E0.MulE (e0, e1) | E0.DivE (e0, e1)
  | E0.EqE (e0, e1)  | E0.NeE (e0, e1)  | E0.GtE (e0, e1)  | E0.LeE (e0, e1) | E0.GtEqE (e0, e1) | E0.LeEqE (e0, e1)
  | E0.ConjE (e0, e1) | E0.DisjE (e0, e1) | E0.ConsE (e0, e1) | E0.PairE (e0, e1) 
    -> Set.union (dollar_e0 e0) (dollar_e0 e1)
  | E0.FunE (_, _, e0) | E0.FunModE (_, _, e0)
  | E0.RunE e0 | E0.NotE e0 | E0.NegE e0
    -> dollar_e0 e0
  | E0.CodE e0  
    -> dollar_e1 e0
  | E0.MatchE (e0, cs0) 
    -> List.fold_right (fun (_, e) -> Set.union (dollar_e0 e)) cs0 (dollar_e0 e0)
  | _ -> Set.empty
and dollar_e1 = function
  | E1.IfE (e0, e1, e2) 
    -> Set.union (dollar_e1 e0) (Set.union (dollar_e1 e1) (dollar_e1 e2))
  | E1.LetE (_, _, _, e0, e1) | E1.LetRecE (_, _, _, e0, e1) | E1.AppE (e0, e1) 
  | E1.AddE (e0, e1) | E1.SubE (e0, e1) | E1.MulE (e0, e1) | E1.DivE (e0, e1)
  | E1.EqE (e0, e1)  | E1.NeE (e0, e1)  | E1.GtE (e0, e1)  | E1.LeE (e0, e1) | E1.GtEqE (e0, e1) | E1.LeEqE (e0, e1)
  | E1.ConjE (e0, e1) | E1.DisjE (e0, e1) | E1.ConsE (e0, e1) | E1.PairE (e0, e1) 
    -> Set.union (dollar_e1 e0) (dollar_e1 e1)
  | E1.FunE (_, _, e0) | E1.NotE e0 | E1.NegE e0 
    -> dollar_e1 e0
  | E1.EscE e0 
    -> dollar_e0 e0
  | E1.MatchE (e0, cs0) 
    -> List.fold_right (fun (_, e) -> Set.union (dollar_e1 e)) cs0 (dollar_e1 e0)
  | _ -> Set.empty