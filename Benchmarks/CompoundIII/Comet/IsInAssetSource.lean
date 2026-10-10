import Benchmarks.CompoundIII.Comet.IsInAssetModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem isInAsset_source (evm : EVM.State) (imms : Store)
    (assets offset reserved : UInt256) (ha : assets.toNat < 2^16)
    (ho : offset.toNat < 2^8) (hr : reserved.toNat < 2^8) :
    ExecFuncBody config (isInAssetEntry imms assets offset reserved) evm
      isInAssetCallable.body (.returned (isInAssetEntry imms assets offset reserved) evm
        (some [.bool (isInAssetBool assets offset reserved)])) := by
  let frame := isInAssetEntry imms assets offset reserved
  have heo : evalExpr? config frame evm (.var "assetOffset") = .ok (.int offset.toNat) := by
    simp only [evalExpr?, frame, isInAssetEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hea : evalExpr? config frame evm (.var "assetsIn") = .ok (.int assets.toNat) := by
    simp only [evalExpr?, frame, isInAssetEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have her : evalExpr? config frame evm (.var "_reserved") = .ok (.int reserved.toNat) := by
    simp only [evalExpr?, frame, isInAssetEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hlt (n : Nat) : evalExpr? config frame evm
      (.binary .lt (.var "assetOffset") (.intLit n)) =
      .ok (.bool (decide (offset.toNat < n))) := by
    simp only [evalExpr?, heo, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]
  apply ExecFuncBody.execBlockRet
  by_cases h16 : offset.toNat < 16
  · rw [isInAssetBool, if_pos h16]
    apply ExecBlock.consReturn
      (ExecStmt.iteTrue (by simpa only [decide_eq_true h16] using hlt 16) ?_)
    exact ABlock.start.returns (bitMembership_source ⟨16, by decide⟩ assets offset.toNat
      ha h16 hea heo)
  · rw [isInAssetBool, if_neg h16]
    have h16' : evalExpr? config frame evm
        (.binary .lt (.var "assetOffset") (.intLit 16)) = .ok (.bool false) := by
      simpa only [decide_eq_false h16] using hlt 16
    by_cases h24 : offset.toNat < 24
    · rw [if_pos h24]
      apply ExecBlock.consReturn (ExecStmt.iteFalse h16' ?_)
      apply ExecBlock.consReturn
        (ExecStmt.iteTrue (by simpa only [decide_eq_true h24] using hlt 24) ?_)
      have hs := checkedNarrowSubSourceOk (cfg := config) (solm := frame) (evm := evm)
        (lhs := .var "assetOffset") (rhs := .intLit 16)
        (a := offset) (b := UInt256.ofNat 16) ⟨8, by decide⟩ heo
        (by simp only [evalExpr?, pure]; rfl) ho (by change 16 ≤ offset.toNat; omega)
      have hs' : evalExpr? config frame evm isInAssetOffsetExpr =
          .ok (.int (Int.ofNat (offset.toNat - 16))) := by
        simpa only [usub_toNat (show (UInt256.ofNat 16).toNat ≤ offset.toNat by
          change 16 ≤ offset.toNat; omega)] using hs
      exact ABlock.start.returns (bitMembership_source ⟨8, by decide⟩ reserved
        (offset.toNat - 16) hr (by change offset.toNat - 16 < 8; omega) her hs')
    · rw [if_neg h24]
      refine ExecBlock.consNormal (solm' := frame) (evm' := evm)
        (ExecStmt.iteFalse h16' ?_) ?_
      · exact ExecBlock.consNormal
          (ExecStmt.iteFalse (by simpa only [decide_eq_false h24] using hlt 24) .nil) .nil
      · exact ABlock.start.returns (by simp only [evalExpr?, pure])

theorem isInAsset_call (frame : Frame) (evm : EVM.State) (assets offset reserved : UInt256)
    (assetExpr offsetExpr reservedExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (ha : assets.toNat < 2^16) (ho : offset.toNat < 2^8) (hr : reserved.toNat < 2^8)
    (hea : evalExpr? config frame evm assetExpr = .ok (.int assets.toNat))
    (heo : evalExpr? config frame evm offsetExpr = .ok (.int offset.toNat))
    (her : evalExpr? config frame evm reservedExpr = .ok (.int reserved.toNat)) :
    ExecStmt config frame evm (.internalCall "isInAsset" [assetExpr, offsetExpr, reservedExpr] ret)
      (.ok { frame with
        locals := frame.locals.insert ret (.bool (isInAssetBool assets offset reserved)) }
        evm) := by
  exact ExecStmt.internalCallReturn (cfg := config) (solm := frame) (evm := evm)
    (args := [assetExpr, offsetExpr, reservedExpr]) (callee := isInAssetCallable)
    (argVals := [.int assets.toNat, .int offset.toNat, .int reserved.toNat])
    (by simp only [evalExprs?, hea, heo, her, pure, bind, EvalResult.bind])
    (by rw [hc]; exact isInAssetCallable_lookup) rfl
    (by simpa only [hc] using isInAsset_source evm frame.immutables assets offset reserved ha ho hr)

end Benchmarks.CompoundIII.Comet
