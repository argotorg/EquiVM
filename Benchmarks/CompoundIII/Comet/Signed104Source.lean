import Benchmarks.CompoundIII.Comet.PrincipalWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def signed104Callable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.uint ⟨104, by decide⟩))⟩]
    returnType := [.elem (.int (.sint ⟨104, by decide⟩))]
    body := [.require (.binary .le (.var "n")
      (.cast (.intLit (2^103 - 1)) (.elem (.int (.uint ⟨104, by decide⟩))))),
      .return [.cast (.var "n") (.elem (.int (.sint ⟨104, by decide⟩)))]] }

theorem signed104Callable_lookup : lookupCallable? contract "signed104" =
    some signed104Callable := rfl

theorem signed104Callable_result (evm : EVM.State) (imms : Store) (n : UInt256) :
    let frame : Frame :=
      { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
    if n.toNat < 2^103 then
      ExecFuncBody config frame evm signed104Callable.body
        (.returned frame evm (some [.int n.toNat]))
    else ExecFuncBody config frame evm signed104Callable.body .reverted := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
  have he : evalExpr? config frame evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, frame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  have hc : evalExpr? config frame evm
      (.binary .le (.var "n") (.cast (.intLit (2^103 - 1)) (.elem (.int (.uint ⟨104, by decide⟩))))) =
      .ok (.bool (decide (n.toNat < 2^103))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, castValue?,
      normalizeInt, evalBinaryOp?, EvalResult.ofOption]
    congr 3
    change ((n.toNat : Int) ≤ 2^103 - 1) = (n.toNat < 2^103)
    apply propext; omega
  split_ifs with hn
  · apply ExecFuncBody.execBlockRet
    apply (ABlock.start.requireStep (hc.trans (by rw [decide_eq_true hn]))).returns
    have hcast := evalExpr_cast_int (intType := .sint ⟨104, by decide⟩) he
    have hnorm : normalizeInt (.sint ⟨104, by decide⟩) (Int.ofNat n.toNat) =
        Int.ofNat n.toNat := by
      simp only [normalizeInt]
      have hm : Int.ofNat n.toNat % Int.ofNat (EVM.twoPow 104) = Int.ofNat n.toNat :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (by
          change n.toNat < 2^104; omega))
      rw [hm]
      exact if_pos (Int.ofNat_lt.mpr hn)
    rw [hnorm] at hcast
    exact hcast
  · apply ExecFuncBody.execBlockRevert
    exact ABlock.start.requireRevert (hc.trans (by rw [decide_eq_false hn]))

theorem signed104_call (frame : Frame) (evm : EVM.State) (n : UInt256)
    (expr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int n.toNat)) :
    ExecStmt config frame evm (.internalCall "signed104" [expr] ret)
      (if n.toNat < 2^103 then
        .ok { frame with locals := frame.locals.insert ret (.int n.toNat) } evm else .reverted) := by
  have hb := signed104Callable_result evm frame.immutables n
  dsimp only at hb
  split_ifs with hn
  · rw [if_pos hn] at hb
    exact ExecStmt.internalCallReturn (callee := signed104Callable)
      (argVals := [.int n.toNat]) (evalExprs?_singleton he)
      (by rw [hc]; exact signed104Callable_lookup) rfl (by simpa only [hc] using hb)
  · rw [if_neg hn] at hb
    exact ExecStmt.internalCallRevert (callee := signed104Callable)
      (argVals := [.int n.toNat]) (evalExprs?_singleton he)
      (by rw [hc]; exact signed104Callable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
