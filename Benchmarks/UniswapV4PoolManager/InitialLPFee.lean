import Benchmarks.UniswapV4PoolManager.LPFeeTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_041

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev initialLPFeeFunction : FunctionDecl := contract.functions[12]!
theorem initialLPFee_lookup : lookupCallable? contract "LPFeeLibrary_getInitialLPFee" =
    some initialLPFeeFunction.toCallable := rfl
def initialLPFeeAllowed (fee : UInt256) : Prop := fee.toNat = 8388608 ∨ fee.toNat ≤ 1000000
instance (fee : UInt256) : Decidable (initialLPFeeAllowed fee) := inferInstanceAs (Decidable (_ ∨ _))
def initialLPFeeWord (fee : UInt256) : UInt256 := if fee.toNat = 8388608 then ⟨0⟩ else fee
def initialLPFeeResult (f : Frame) (evm : EVM.State) (fee : UInt256) : ExecResult :=
  if initialLPFeeAllowed fee then .returned f evm (some [.int (Int.ofNat (initialLPFeeWord fee).toNat)]) else .reverted

theorem initialLPFeeWord_bound {fee : UInt256} (h : initialLPFeeAllowed fee) :
    (initialLPFeeWord fee).toNat < 2^24 := by
  unfold initialLPFeeWord
  split
  · decide
  · unfold initialLPFeeAllowed at h
    omega

theorem initialLPFeeBody {f : Frame} {evm : EVM.State} {fee : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.int (Int.ofNat fee.toNat))) :
    ∃ f', ExecFuncBody config f evm initialLPFeeFunction.body (initialLPFeeResult f' evm fee) := by
  let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool (decide (fee.toNat = 8388608)))}
  have hcall := lpFeeDynamicCall (evm := evm) hf (evalLocalValue hs) "__c0"
  have hcond := evalLocalValue (cfg := config) (f := f1) (evm := evm) (store_get_self _ _ _)
  by_cases hd : fee.toNat = 8388608
  · simp only [hd, decide_true] at hcond
    simp only [initialLPFeeResult, initialLPFeeAllowed, hd, true_or, if_true, initialLPFeeWord, if_pos hd]
    exact ⟨_, .execBlockRet (ExecBlock.consNormal hcall (ExecBlock.consReturn
      (ExecStmt.iteTrue hcond (ABlock.start.returns (by simp only [evalExpr?, pure]; rfl)))))⟩
  · simp only [hd, decide_false] at hcond
    have hs1 : f1.locals.get? "self" = some (.int (Int.ofNat fee.toNat)) :=
      (store_get_ne _ _ (by decide : ("__c0" == "self") = false)).trans hs
    have hvalidate := lpFeeValidateCall (f := f1) (evm := evm) hf (evalLocalValue hs1) "__c1"
    by_cases hv : fee.toNat ≤ 1000000
    · simp only [if_pos hv] at hvalidate
      simp only [initialLPFeeResult, initialLPFeeAllowed, hd, hv, false_or, if_true, initialLPFeeWord, if_neg hd]
      exact ⟨_, .execBlockRet (ExecBlock.consNormal hcall (ExecBlock.consNormal
        (ExecStmt.iteFalse hcond ExecBlock.nil) (ExecBlock.consNormal hvalidate
          (ABlock.start.returns (evalLocalValue ((store_get_ne _ _
            (by decide : ("__c1" == "self") = false)).trans hs1))))))⟩
    · simp only [if_neg hv] at hvalidate
      simp only [initialLPFeeResult, initialLPFeeAllowed, hd, hv, false_or, if_false]
      exact ⟨f1, .execBlockRevert (ExecBlock.consNormal hcall (ExecBlock.consNormal
        (ExecStmt.iteFalse hcond ExecBlock.nil) (ExecBlock.consRevert hvalidate)))⟩

theorem initialLPFeeCall {f : Frame} {evm : EVM.State} {e : Expr} {fee : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "LPFeeLibrary_getInitialLPFee" [e] retVar)
      (if initialLPFeeAllowed fee then
        .ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (initialLPFeeWord fee).toNat))} evm else .reverted) := by
  obtain ⟨f', hb⟩ := initialLPFeeBody
    (f := {f with locals := (∅ : Store).insert "self" (.int (Int.ofNat fee.toNat))}) (evm := evm) hf (store_get_self _ _ _)
  have hl : lookupCallable? f.contract "LPFeeLibrary_getInitialLPFee" = some initialLPFeeFunction.toCallable := by
    rw [hf]; exact initialLPFee_lookup
  by_cases hv : initialLPFeeAllowed fee
  · simp only [initialLPFeeResult, if_pos hv] at hb ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hl rfl hb
  · simp only [initialLPFeeResult, if_neg hv] at hb ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hl rfl hb

theorem initialLPFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hc : fee.toNat < 2^24)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨14965⟩ (fee :: ret :: R) mem aw rdata σ k C) :
    if initialLPFeeAllowed fee then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (initialLPFeeWord fee :: R) mem aw rdata σ k' C' else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land fee (UInt256.ofNat 16777215) = fee := u256LandMaskCleanOfToNat _ _ rfl hc
  by_cases hd : fee.toNat = 8388608
  · simp only [initialLPFeeAllowed, hd, true_or, if_true, initialLPFeeWord, if_pos hd]
    have he : fee = UInt256.ofNat 8388608 := u256_inj hd
    have rd1 := poolManagerBlocks.poolManager_block_14965_taken (by simp only [List.length_cons]; omega)
      (by rw [hclean, he, u256_eq_refl]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, poolManagerBlocks.poolManager_block_14989 (by omega) hret rd1⟩
  · simp only [initialLPFeeAllowed, hd, false_or, initialLPFeeWord, if_neg hd]
    have he : fee ≠ UInt256.ofNat 8388608 := fun he => hd (congrArg UInt256.toNat he)
    have rd1 := poolManagerBlocks.poolManager_block_14965_fallthrough (by simp only [List.length_cons]; omega)
      (by rw [hclean]; exact u256_eq_of_ne he) h
    have rd2 := poolManagerBlocks.poolManager_block_14981 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hval := lpFeeValidateTrace v (by change R.length+6 ≤ 1024; exact hstack) hc
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
    by_cases hv : fee.toNat ≤ 1000000
    · simp only [if_pos hv] at hval ⊢
      obtain ⟨k3, C3, rd3⟩ := hval
      exact ⟨_, _, poolManagerBlocks.poolManager_block_13903 (by omega) hret rd3⟩
    · simpa only [if_neg hv] using hval

end Benchmarks.UniswapV4PoolManager
