import Benchmarks.UniswapV4PoolManager.CurrencyTransferABI
import Benchmarks.UniswapV4PoolManager.LocalBytes
import Benchmarks.UniswapV4PoolManager.CallComposition
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev currencyTransferFunction : FunctionDecl := contract.functions[41]!
theorem currencyTransfer_lookup : lookupCallable? contract "CurrencyLibrary_transfer" =
    some currencyTransferFunction.toCallable := rfl

def transferReturnValid (out : ByteArray) : Prop :=
  out.size = 0 ∨ (32 ≤ out.size ∧ returnedBalanceWord out = ⟨1⟩)
instance (out : ByteArray) : Decidable (transferReturnValid out) := inferInstanceAs (Decidable (_ ∨ _))

def transferReturnStatements : List Stmt :=
  [.letDecl "validReturn" (some (.elem .bool))
     (.binary .eq (.arrayLength .localVar ⟨"returned", []⟩) (.intLit 0)),
   .ite (.binary .gt (.arrayLength .localVar ⟨"returned", []⟩) (.intLit 31))
     [.assign .localVar ⟨"validReturn", []⟩ (.binary .eq
       (.abiDecode abiUInt256 (.bytesSlice (.var "returned") (.intLit 0) (.intLit 32))) (.intLit 1))] [],
   .require (.binary .and (.var "validReturn") (.var "success"))]

theorem transferReturnBody {f : Frame} {evm : EVM.State} {z : Bool} {out : ByteArray}
    (hb : f.locals.get? "returned" = some (.bytes out))
    (hz : f.locals.get? "success" = some (.bool z)) :
    ∃ f', ExecBlock config f evm transferReturnStatements
      (if z = true ∧ transferReturnValid out then .ok f' evm else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "validReturn" (.bool (decide (out.size = 0)))}
  let f2 : Frame := if 32 ≤ out.size then
    {f1 with locals := f1.locals.insert "validReturn" (.bool (decide (returnedBalanceWord out = ⟨1⟩)))} else f1
  have hlet : ExecStmt config f evm transferReturnStatements[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (evalNatEqLiteral (evalLocalBytesLength hb))
  have hb1 : f1.locals.get? "returned" = some (.bytes out) :=
    (store_get_ne _ _ (by decide : ("validReturn" == "returned") = false)).trans hb
  have hg := evalNatGtLiteral (cfg := config) (k := 31) (evm := evm) (evalLocalBytesLength hb1)
  have hite : ExecStmt config f1 evm transferReturnStatements[1]! (.ok f2 evm) := by
    by_cases hlo : 32 ≤ out.size
    · rw [decide_eq_true (by omega : 31 < out.size)] at hg
      apply ExecStmt.iteTrue hg
      have hdecode := evalDecodeUint256Prefix (cfg := config) (evm := evm) rfl (evalLocalValue hb1) hlo
      have heq := evalNatEqLiteral (k := 1) hdecode
      have hword : (returnedBalanceWord out).toNat = 1 ↔ returnedBalanceWord out = ⟨1⟩ :=
        ⟨fun h => u256_inj h, fun h => by rw [h]; rfl⟩
      change evalExpr? config f1 evm _ = .ok (.bool (decide ((returnedBalanceWord out).toNat = 1))) at heq
      simp only [hword] at heq
      simpa only [f2, if_pos hlo] using execBlock_singleton
        (ExecStmt.assign heq (assignLocalValue (store_get_self _ _ _)))
    · rw [decide_eq_false (by omega : ¬ 31 < out.size)] at hg
      simpa only [f2, if_neg hlo] using ExecStmt.iteFalse hg (ExecBlock.nil (cfg := config))
  have hvalid : f2.locals.get? "validReturn" = some (.bool (decide (transferReturnValid out))) := by
    by_cases hlo : 32 ≤ out.size
    · simp only [f2, if_pos hlo, store_get_self, transferReturnValid, hlo, true_and,
        show out.size ≠ 0 by omega, false_or]
    · simp only [f2, if_neg hlo, f1, store_get_self, transferReturnValid, hlo, false_and, or_false]
  have hz1 : f1.locals.get? "success" = some (.bool z) :=
    (store_get_ne _ _ (by decide : ("validReturn" == "success") = false)).trans hz
  have hz2 : f2.locals.get? "success" = some (.bool z) := by
    by_cases hlo : 32 ≤ out.size
    · simp only [f2, if_pos hlo]
      exact (store_get_ne _ _ (by decide : ("validReturn" == "success") = false)).trans hz1
    · simpa only [f2, if_neg hlo] using hz1
  have hrequire := evalAndBool (cfg := config) (evm := evm) (evalLocalValue hvalid) (evalLocalValue hz2)
  refine ⟨f2, ExecBlock.consNormal hlet (ExecBlock.consNormal hite ?_)⟩
  cases z <;> by_cases hv : transferReturnValid out <;> simp only [hv, decide_true, decide_false,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, and_true, and_false,
    if_true, if_false] at hrequire ⊢
  · exact ExecBlock.consRevert (ExecStmt.requireFalse hrequire)
  · exact ExecBlock.consRevert (ExecStmt.requireFalse hrequire)
  · exact ExecBlock.consNormal (ExecStmt.requireTrue hrequire) ExecBlock.nil
  · exact ExecBlock.consRevert (ExecStmt.requireFalse hrequire)

theorem currencyTransferNativeBody {f : Frame} {evm evm' : EVM.State}
    {recipient : AccountAddress} {amount : UInt256} {z : Bool} {out : ByteArray}
    (hc : f.locals.get? "currency" = some (.address (AccountAddress.ofNat 0)))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hcall : callViaEVM evm recipient (Int.ofNat amount.toNat) .empty (z, evm', out)) :
    ∃ f', ExecFuncBody config f evm currencyTransferFunction.body
      (if z then .returned f' evm' none else .reverted) := by
  let f' : Frame := {f with locals := (f.locals.insert "success" (.bool z)).insert "returned" (.bytes out)}
  have hguard := evalEqAddress (evm := evm) (evalLocalValue hc) (evalAddressLiteral config f evm (.ofNat 0))
  have hlow : ExecStmt config f evm (.lowLevelCall (.var "to") (.var "amount") (.bytesLit .empty) "success" "returned")
      (.ok f' evm') := lowLevelCallSource (evalLocalValue ht) (evalLocalValue ha)
        (by simp only [evalExpr?, pure]) hcall
  have hsuccess : evalExpr? config f' evm' (.var "success") = .ok (.bool z) :=
    evalLocalValue ((store_get_ne _ _ (by decide : ("returned" == "success") = false)).trans (store_get_self _ _ _))
  simp only [decide_true] at hguard
  refine ⟨f', ?_⟩
  cases z with
  | false => exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue hguard
      (ExecBlock.consNormal hlow (ExecBlock.consRevert (ExecStmt.requireFalse hsuccess)))))
  | true => exact .execBlockOK (ExecBlock.consNormal (ExecStmt.iteTrue hguard
      (ExecBlock.consNormal hlow (ExecBlock.consNormal (ExecStmt.requireTrue hsuccess) ExecBlock.nil))) ExecBlock.nil)

theorem currencyTransferNativeStatic {f : Frame} {evm : EVM.State} {recipient : AccountAddress} {amount : UInt256}
    (hc : f.locals.get? "currency" = some (.address (AccountAddress.ofNat 0)))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hamount : amount ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config f evm currencyTransferFunction.body .staticViolation := by
  have hguard := evalEqAddress (evm := evm) (evalLocalValue hc) (evalAddressLiteral config f evm (.ofNat 0))
  simp only [decide_true] at hguard
  exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.iteTrue hguard
    (ExecBlock.consStatic (ExecStmt.lowLevelCallStatic (evalLocalValue ht) (evalLocalValue ha)
      (by simp only [evalExpr?, pure]; rfl) (by simpa only [wordOfInt_ofNat_toNat] using hamount) hperm))))

theorem currencyTransferTokenBody {f : Frame} {evm evm' : EVM.State}
    {currency recipient : AccountAddress} {amount : UInt256} {z : Bool} {out : ByteArray}
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "to" = some (.address recipient))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hn : currency ≠ AccountAddress.ofNat 0)
    (hcall : callViaEVM evm currency 0 (transferPayload recipient amount) (z, evm', out)) :
    ∃ f', ExecFuncBody config f evm currencyTransferFunction.body
      (if z = true ∧ transferReturnValid out then .returned f' evm' none else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "payload" (.bytes (transferPayload recipient amount))}
  let f2 : Frame := {f1 with locals := (f1.locals.insert "success" (.bool z)).insert "returned" (.bytes out)}
  have hguard := evalEqAddress (evm := evm) (evalLocalValue hc) (evalAddressLiteral config f evm (.ofNat 0))
  rw [decide_eq_false hn] at hguard
  have hlet : ExecStmt config f evm (.letDecl "payload" (some .bytes) transferPayloadExpr) (.ok f1 evm) :=
    ExecStmt.letDecl (evalTransferPayload ht ha)
  have hlow : ExecStmt config f1 evm (.lowLevelCall (.var "currency") (.intLit 0) (.var "payload") "success" "returned")
      (.ok f2 evm') := lowLevelCallSource
        (evalLocalValue ((store_get_ne _ _ (by decide : ("payload" == "currency") = false)).trans hc))
        (by simp only [evalExpr?, pure]) (evalLocalValue (store_get_self _ _ _)) hcall
  obtain ⟨f', hrest⟩ := transferReturnBody (f := f2) (evm := evm') (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("returned" == "success") = false)).trans (store_get_self _ _ _))
  refine ⟨f', ?_⟩
  by_cases hgood : z = true ∧ transferReturnValid out
  · rw [if_pos hgood] at hrest ⊢
    exact .execBlockOK (ExecBlock.consNormal (ExecStmt.iteFalse hguard
      (ExecBlock.consNormal hlet (ExecBlock.consNormal hlow hrest))) ExecBlock.nil)
  · rw [if_neg hgood] at hrest ⊢
    exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteFalse hguard
      (ExecBlock.consNormal hlet (ExecBlock.consNormal hlow hrest))))

end Benchmarks.UniswapV4PoolManager
