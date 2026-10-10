import Benchmarks.CompoundIII.Comet.ArithmeticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES safe64Callable to the uint104 and uint128 guards used by base and collateral flows.
def safeUintCallable (width : BitWidth) : CallableDecl :=
  { params := [⟨"n", abiUInt256⟩], returnType := [.elem (.int (.uint width))]
    body := [.require (.binary .le (.var "n") (.intLit (Int.ofNat (2^width.val - 1)))),
      .return [.cast (.var "n") (.elem (.int (.uint width)))]] }

theorem safe104Callable_lookup : lookupCallable? contract "safe104" =
    some (safeUintCallable ⟨104, by decide⟩) := rfl

theorem safe128Callable_lookup : lookupCallable? contract "safe128" =
    some (safeUintCallable ⟨128, by decide⟩) := rfl

theorem safeUintCallable_result (width : BitWidth) (evm : EVM.State) (imms : Store)
    (n : UInt256) :
    let frame : Frame :=
      { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
    if n.toNat < 2^width.val then
      ExecFuncBody config frame evm (safeUintCallable width).body
        (.returned frame evm (some [.int n.toNat]))
    else ExecFuncBody config frame evm (safeUintCallable width).body .reverted := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := (∅ : Store).insert "n" (.int n.toNat), immutables := imms }
  have he : evalExpr? config frame evm (.var "n") = .ok (.int (Int.ofNat n.toNat)) := by
    simp only [evalExpr?, frame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  have hc := naturalLeSource he (cfg := config) (frame := frame) (evm := evm)
    (rhs := .intLit (Int.ofNat (2^width.val - 1))) (b := 2^width.val - 1)
    (by simp only [evalExpr?, pure])
  have hpow : 0 < 2^width.val := by positivity
  split_ifs with hn
  · apply ExecFuncBody.execBlockRet
    apply (ABlock.start.requireStep (hc.trans (by rw [decide_eq_true (by omega)]))).returns
    have hcast := evalExpr_cast_int (intType := .uint width) he
    have hnorm : normalizeInt (.uint width) (Int.ofNat n.toNat) = Int.ofNat n.toNat :=
      normalizeInt_uint_eq_self width _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hn)
    rw [hnorm] at hcast
    exact hcast
  · apply ExecFuncBody.execBlockRevert
    exact ABlock.start.requireRevert (hc.trans (by rw [decide_eq_false (by omega)]))

theorem safeUint_call (width : BitWidth) (name : Ident)
    (hlookup : lookupCallable? contract name = some (safeUintCallable width))
    (frame : Frame) (evm : EVM.State) (n : UInt256) (expr : Expr) (ret : Ident)
    (hc : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.int n.toNat)) :
    ExecStmt config frame evm (.internalCall name [expr] ret)
      (if n.toNat < 2^width.val then
        .ok { frame with locals := frame.locals.insert ret (.int n.toNat) } evm else .reverted) := by
  have hb := safeUintCallable_result width evm frame.immutables n
  dsimp only at hb
  split_ifs with hn
  · rw [if_pos hn] at hb
    exact ExecStmt.internalCallReturn (callee := safeUintCallable width)
      (argVals := [.int n.toNat]) (evalExprs?_singleton he)
      (by rw [hc]; exact hlookup) rfl (by simpa only [hc] using hb)
  · rw [if_neg hn] at hb
    exact ExecStmt.internalCallRevert (callee := safeUintCallable width)
      (argVals := [.int n.toNat]) (evalExprs?_singleton he)
      (by rw [hc]; exact hlookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
