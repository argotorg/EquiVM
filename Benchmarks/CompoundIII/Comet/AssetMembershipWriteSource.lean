import Benchmarks.CompoundIII.Comet.AssetMembershipModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- GENERALIZES internalBlockResult.iteTrue to the false branch.
theorem internalBlockResult.iteFalse {cfg frame evm cond yes no result}
    (hc : evalExpr? cfg frame evm cond = .ok (.bool false))
    (hb : internalBlockResult cfg frame evm no result) :
    internalBlockResult cfg frame evm [.ite cond yes no] result := by
  cases result with
  | ok evm' =>
      obtain ⟨frame', hb⟩ := hb
      exact ⟨frame', ExecBlock.consNormal (ExecStmt.iteFalse hc hb) ExecBlock.nil⟩
  | reverted => exact ExecBlock.consRevert (ExecStmt.iteFalse hc hb)
  | staticViolation => exact ExecBlock.consStatic (ExecStmt.iteFalse hc hb)

theorem userBasicBitUpdate_source (frame : Frame) (evm : EVM.State)
    (account : AccountAddress) (i : Fin 4) (add : Bool) (bit : Nat) (bitExpr : Expr)
    (hc : frame.contract = contract) (hu : frame.locals.get? "userBasic" = none)
    (ha : evalExpr? config frame evm (.var "account") = .ok (.address account))
    (hb : bit < (userBasicFieldWidth i).val)
    (he : evalExpr? config frame evm bitExpr = .ok (.int (Int.ofNat bit))) :
    internalBlockResult config frame evm
      [.assign .storage ⟨"userBasic", [.mindex (.var "account"), .field (userBasicFieldName i)]⟩
        (typedBitUpdateExpr add (userBasicFieldWidth i)
          (.storage ⟨"userBasic", [.mindex (.var "account"), .field (userBasicFieldName i)]⟩)
          bitExpr)]
      (if evm.executionEnv.perm then
        .ok (storePackedWord evm (userBasicSlot account)
          (typedBitUpdateWord add (userBasicFieldWidth i)
            (userBasicFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (userBasicSlot account)) i) bit)
          (userBasicFieldOffset i).val (userBasicFieldSize i).val)
        else .staticViolation) := by
  have hr := evalUserBasicFieldOf frame evm account (.var "account") i hc hu ha
  have hv : (userBasicFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (userBasicSlot account)) i).toNat < 2^(userBasicFieldWidth i).val :=
    packedUint_lt _ _ (by fin_cases i <;> decide)
  have hx := typedBitUpdate_source add (userBasicFieldWidth i) _ bit hv hb hr he
  have hw := assignUserBasicField frame evm account (.var "account") i
    (typedBitUpdateWord add (userBasicFieldWidth i)
      (userBasicFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (userBasicSlot account)) i) bit) hc hu ha
  cases hp : evm.executionEnv.perm
  · simp only [Bool.false_eq_true, if_false, internalBlockResult]
    exact ExecBlock.consStatic (ExecStmt.assignStatic hx hw hp)
  · simp only [if_true, internalBlockResult]
    exact ⟨frame, ExecBlock.consNormal (ExecStmt.assign hx hw) .nil⟩

theorem assetMembershipWrite_source (frame : Frame) (evm : EVM.State)
    (account : AccountAddress) (offset : UInt256) (add : Bool)
    (hc : frame.contract = contract) (hu : frame.locals.get? "userBasic" = none)
    (ha : evalExpr? config frame evm (.var "account") = .ok (.address account))
    (ho : offset.toNat < 2^8)
    (he : evalExpr? config frame evm assetMembershipOffset = .ok (.int offset.toNat)) :
    internalBlockResult config frame evm (assetMembershipWriteBlock add)
      (assetMembershipWriteResult evm account offset add) := by
  have hlt (n : Nat) : evalExpr? config frame evm
      (.binary .lt assetMembershipOffset (.intLit n)) =
      .ok (.bool (decide (offset.toNat < n))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]
  by_cases h16 : offset.toNat < 16
  · have h24 : offset.toNat < 24 := by omega
    simp only [assetMembershipWriteResult, h24, if_true, assetMembershipState, h16]
    apply internalBlockResult.iteTrue (by simpa only [decide_eq_true h16] using hlt 16)
    exact userBasicBitUpdate_source frame evm account 2 add offset.toNat
      assetMembershipOffset hc hu ha h16 he
  · have h16' : evalExpr? config frame evm
        (.binary .lt assetMembershipOffset (.intLit 16)) = .ok (.bool false) := by
      simpa only [decide_eq_false h16] using hlt 16
    apply internalBlockResult.iteFalse h16'
    by_cases h24 : offset.toNat < 24
    · simp only [assetMembershipWriteResult, h24, if_true, assetMembershipState, h16, if_false]
      apply internalBlockResult.iteTrue (by simpa only [decide_eq_true h24] using hlt 24)
      have hs := checkedNarrowSubSourceOk (cfg := config) (solm := frame) (evm := evm)
        (lhs := assetMembershipOffset) (rhs := .intLit 16)
        (a := offset) (b := UInt256.ofNat 16) ⟨8, by decide⟩ he
        (by simp only [evalExpr?, pure]; rfl) ho
        (by change 16 ≤ offset.toNat; omega)
      have he' : evalExpr? config frame evm (assetMembershipBitExpr true) =
          .ok (.int (Int.ofNat (offset.toNat - 16))) := by
        simpa only [usub_toNat (show (UInt256.ofNat 16).toNat ≤ offset.toNat by
          change 16 ≤ offset.toNat; omega)] using hs
      exact userBasicBitUpdate_source frame evm account 3 add (offset.toNat - 16)
        (assetMembershipBitExpr true) hc hu ha (by change offset.toNat - 16 < 8; omega) he'
    · simp only [assetMembershipWriteResult, h24, if_false]
      apply internalBlockResult.iteFalse (by simpa only [decide_eq_false h24] using hlt 24)
      exact ⟨frame, ExecBlock.nil⟩

end Benchmarks.CompoundIII.Comet
