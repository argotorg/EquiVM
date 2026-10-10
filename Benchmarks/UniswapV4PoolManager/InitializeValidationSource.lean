import Benchmarks.UniswapV4PoolManager.HookValidationSource
import Benchmarks.UniswapV4PoolManager.InitialLPFee
import Benchmarks.UniswapV4PoolManager.PoolKeySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def initializeKeyValid (key : PoolKeyWords) : Prop :=
  EVM.signed key.tickSpacing ≤ 32767 ∧ 1 ≤ EVM.signed key.tickSpacing ∧
  key.currency0.toNat < key.currency1.toNat ∧ hookAddressValid key.hooks key.fee = true ∧
  initialLPFeeAllowed key.fee
instance (key : PoolKeyWords) : Decidable (initializeKeyValid key) :=
  inferInstanceAs (Decidable (_ ∧ _))

def initializeValidationFrame (f : Frame) (key : PoolKeyWords) : Frame :=
  {f with locals := ((f.locals.insert "__c1" (.bool (hookAddressValid key.hooks key.fee))).insert
    "lpFee" (.int (Int.ofNat (initialLPFeeWord key.fee).toNat)))}

theorem initializeValidationSource {f : Frame} {evm : EVM.State} {key : PoolKeyWords}
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (hk : f.locals.get? "key" = some (poolKeyValue key)) :
    if initializeKeyValid key then
      ExecBlock config f evm ((initializeTransition.body.drop 6).take 6)
        (.ok (initializeValidationFrame f key) evm)
    else ExecFuncBody config f evm (initializeTransition.body.drop 6) .reverted := by
  have hkey := evalLocalValue (cfg := config) (evm := evm) hk
  have hspacing := evalStructField hkey (field := "tickSpacing") rfl
  have hgt : evalExpr? config f evm (.binary .gt (.field (.var "key") "tickSpacing") (.intLit 32767)) =
      .ok (.bool (decide (32767 < EVM.signed key.tickSpacing))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hspacing]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  have hlt : evalExpr? config f evm (.binary .lt (.field (.var "key") "tickSpacing") (.intLit 1)) =
      .ok (.bool (decide (EVM.signed key.tickSpacing < 1))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hspacing]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  have hge : evalExpr? config f evm (.binary .ge (.field (.var "key") "currency0")
      (.field (.var "key") "currency1")) =
      .ok (.bool (decide (key.currency1.toNat ≤ key.currency0.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide),
      evalStructField hkey (field := "currency0") rfl, evalStructField hkey (field := "currency1") rfl]
    change EvalResult.ok (Value.bool (decide (key.currency0.toNat % 2^160 ≥ key.currency1.toNat % 2^160))) = _
    rw [Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hc.2.1]
  have hcall := hookValidationCall hf (evalStructField hkey (field := "hooks") rfl)
    (evalStructField hkey (field := "fee") rfl) "__c1"
  have hword : accountWord (AccountAddress.ofNat key.hooks.toNat) = key.hooks :=
    (accountWord_fromId _).trans (solcAddrMask_clean hc.2.2.2.2)
  rw [hword] at hcall
  let f1 : Frame := {f with locals := f.locals.insert "__c1" (.bool (hookAddressValid key.hooks key.fee))}
  have hnot := evalNotBool (evalLocalValue (cfg := config) (f := f1) (evm := evm)
    (store_get_self _ _ _))
  have hfee := initialLPFeeCall (f := f1) (evm := evm) hf
    (evalStructField (evalLocalValue ((store_get_ne _ _
      (by decide : ("__c1" == "key") = false)).trans hk)) (field := "fee") rfl) "lpFee"
  by_cases h0 : EVM.signed key.tickSpacing ≤ 32767
  · rw [decide_eq_false (by omega : ¬32767 < EVM.signed key.tickSpacing)] at hgt
    have hs0 := ExecStmt.iteFalse (thenB := [.require (.boolLit false)]) hgt ExecBlock.nil
    by_cases h1 : 1 ≤ EVM.signed key.tickSpacing
    · rw [decide_eq_false (by omega : ¬EVM.signed key.tickSpacing < 1)] at hlt
      have hs1 := ExecStmt.iteFalse (thenB := [.require (.boolLit false)]) hlt ExecBlock.nil
      by_cases h2 : key.currency0.toNat < key.currency1.toNat
      · rw [decide_eq_false (by omega : ¬key.currency1.toNat ≤ key.currency0.toNat)] at hge
        have hs2 := ExecStmt.iteFalse (thenB := [.require (.boolLit false)]) hge ExecBlock.nil
        by_cases h3 : hookAddressValid key.hooks key.fee = true
        · simp only [h3, Bool.not_true] at hnot
          have hs3 := ExecStmt.iteFalse (thenB := [.require (.boolLit false)]) hnot ExecBlock.nil
          by_cases h4 : initialLPFeeAllowed key.fee
          · rw [if_pos (show initializeKeyValid key from ⟨h0, h1, h2, h3, h4⟩)]
            rw [if_pos h4] at hfee
            exact ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
              (ExecBlock.consNormal hcall (ExecBlock.consNormal hs3 (execBlock_singleton hfee)))))
          · rw [if_neg (fun hh => h4 hh.2.2.2.2)]
            rw [if_neg h4] at hfee
            exact .execBlockRevert (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1
              (ExecBlock.consNormal hs2 (ExecBlock.consNormal hcall (ExecBlock.consNormal hs3
                (ExecBlock.consRevert hfee))))))
        · rw [if_neg (fun hh => h3 hh.2.2.2.1)]
          have hfalse : hookAddressValid key.hooks key.fee = false := Bool.eq_false_iff.mpr h3
          simp only [hfalse, Bool.not_false] at hnot
          exact .execBlockRevert (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1
            (ExecBlock.consNormal hs2 (ExecBlock.consNormal hcall (ExecBlock.consRevert
              (ExecStmt.iteTrue hnot (ExecBlock.consRevert (ExecStmt.requireFalse
                (by simp only [evalExpr?, pure])))))))))
      · rw [if_neg (fun hh => h2 hh.2.2.1)]
        rw [decide_eq_true (by omega : key.currency1.toNat ≤ key.currency0.toNat)] at hge
        exact .execBlockRevert (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1
          (ExecBlock.consRevert (ExecStmt.iteTrue hge (ExecBlock.consRevert
            (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))
    · rw [if_neg (fun hh => h1 hh.2.1)]
      rw [decide_eq_true (by omega : EVM.signed key.tickSpacing < 1)] at hlt
      exact .execBlockRevert (ExecBlock.consNormal hs0 (ExecBlock.consRevert
        (ExecStmt.iteTrue hlt (ExecBlock.consRevert (ExecStmt.requireFalse
          (by simp only [evalExpr?, pure]))))))
  · rw [if_neg (fun hh => h0 hh.1)]
    rw [decide_eq_true (by omega : 32767 < EVM.signed key.tickSpacing)] at hgt
    exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue hgt
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))

end Benchmarks.UniswapV4PoolManager
