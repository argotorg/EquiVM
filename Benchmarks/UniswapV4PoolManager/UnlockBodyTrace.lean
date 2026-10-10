import Benchmarks.UniswapV4PoolManager.UnlockFinishTrace
import Benchmarks.UniswapV4PoolManager.UnlockOpenTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem unlockBodyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw saved : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hd : f.locals.get? "data" = some (.bytes (calldataBytesPayload I.calldata)))
    (hb : BytesCalldataBounds I.calldata)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hpaid : 552+Cₘ aw ≤ C) (hmem : mem.size = 96) (hfree : memLoad ⟨64⟩ mem = ⟨160⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨8889⟩
      (calldataWord I.calldata (4+(calldataWord I.calldata 4).toNat) ::
        (⟨4⟩+calldataWord I.calldata 4+⟨32⟩) :: saved :: R) mem aw rdata evm.accountMap k C) :
    (X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
      ∃ result, ExecFuncBody config f evm (unlockTransition.body.drop 3) result ∧
        bytesResultTrace (deployedRuntime v) g s0 result := by
  have hpref := unlockPrefix (evm := evm) hf
  rw [hI] at hpref
  have ht := transientWord_accountMap hI lockSlot
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  swap
  · rw [if_neg hl] at hpref
    have rd1 := poolManager_block_8889_taken (by simp only [List.length_cons]; omega)
      (by change codeOwnerTransientWord I evm.accountMap lockSlot ≠ ⟨0⟩; rw [← ht]; exact hl)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inr ⟨.reverted, .execBlockRevert
      (execBlock_reverted_append (s2 := unlockTransition.body.drop 8) hpref),
      poolManager_block_9421 (by simp only [List.length_cons]; omega) rd1⟩
  rw [if_pos hl] at hpref
  have rdOpen := poolManager_block_8889_fallthrough (by simp only [List.length_cons]; omega)
    (by change codeOwnerTransientWord I evm.accountMap lockSlot = ⟨0⟩; rw [← ht]; exact hl) h
  by_cases hp : I.perm = false
  · rw [if_pos hp] at hpref
    exact .inr ⟨.staticViolation, .execBlockStatic
      (execBlock_append_term (s2 := unlockTransition.body.drop 8) hpref (by intro _ _ he; cases he)),
      unlockOpenStatic v (by simp only [List.length_cons]; omega) hp rdOpen⟩
  rw [if_neg hp] at hpref
  have hp' : I.perm = true := Bool.eq_true_of_not_eq_false hp
  let len := calldataWord I.calldata (4+(calldataWord I.calldata 4).toNat)
  let src : UInt256 := ⟨4⟩+calldataWord I.calldata 4+⟨32⟩
  have hlen : len.toNat ≤ solcMaxU64 := hb.2.2.2.2.1
  have hsrc : src.toNat = 4+(calldataWord I.calldata 4).toNat+32 := by
    have ho := add4_word_toNat (calldataWord I.calldata 4) hb.2.2.1
    change (UInt256.ofNat 4+calldataWord I.calldata 4).toNat = 4+(calldataWord I.calldata 4).toNat at ho
    have hfit : (UInt256.ofNat 4+calldataWord I.calldata 4).toNat+32 < UInt256.size := by
      rw [ho]
      change _ < 2^256
      have hh := hb.2.2.1
      change _ ≤ 2^64-1 at hh
      omega
    change ((UInt256.ofNat 4+calldataWord I.calldata 4)+UInt256.ofNat 32).toNat = _
    rw [uadd_word_ofNat_toNat _ 32 hfit, ho]
  have hslice : src.toNat+len.toNat ≤ I.calldata.size := by
    rw [hsrc]
    exact hb.2.2.2.2.2
  obtain ⟨aw', k', C', hcost, rdCall⟩ := unlockOpenTrace v
    (by simp only [List.length_cons]; omega) hI hp' hmem hfree hlen rdOpen
  let mem' := bytesCallMemory I.calldata mem 160 src.toNat unlockCallbackSelectorWord len
  let ending := UInt256.ofNat (228+paddedSize len.toNat)
  have hpad := paddedSize_le_add31 len.toNat
  have hend : (UInt256.sub ending ⟨160⟩).toNat = 68+paddedSize len.toNat := by
    have he : ending.toNat = 228+paddedSize len.toNat := UInt256.toNat_ofNat_of_lt (by
      change _ < 2^256; change _ ≤ 2^64-1 at hlen; omega)
    rw [usub_toNat (by rw [he]; change 160 ≤ _; omega), he]
    change 228+paddedSize len.toNat-160 = _
    omega
  have hrequest : mem'.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat =
      unlockCallbackSelector++bytesReturnEncoding (calldataBytesPayload I.calldata) := by
    rw [hend, bytesCallMemory_read _ _ _ _ _ _ (by rw [hmem]; decide)
      (by rw [hmem]; exact (by native_decide)) hslice,
      show unlockCallbackSelectorWord.toByteArray.extract 0 4 = unlockCallbackSelector from by decide +kernel,
      hsrc]
    rfl
  have hsize : 160 ≤ mem'.size := by
    rw [bytesCallMemory_size _ _ _ _ _ _ (by rw [hmem]; decide) (by rw [hmem]; exact (by native_decide)) hslice]
    omega
  have hsmall : (mem'.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat).size ≤
      maxReturnDataSizeByGas := by
    apply ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas
    rw [hend]
    change _ ≤ 32*7699711013376144369441080719284001820899
    change _ ≤ 2^64-1 at hlen
    omega
  let f' := unlockPrefixFrame f I.source
  have hcaller : f'.locals.get? "caller" = some (.address I.source) := store_get_self _ _ _
  have hdata : f'.locals.get? "data" = some (.bytes (calldataBytesPayload I.calldata)) :=
    (store_get_ne _ _ (by decide : ("caller" == "data") = false)).trans
      ((store_get_ne _ _ (by decide : ("__c1" == "data") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c0" == "data") = false)).trans
          ((store_get_ne _ _ (by decide : ("result" == "data") = false)).trans hd)))
  have hresult : f'.locals.get? "result" = some (.bytes .empty) :=
    (store_get_ne _ _ (by decide : ("caller" == "result") = false)).trans
      ((store_get_ne _ _ (by decide : ("__c1" == "result") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c0" == "result") = false)).trans (store_get_self _ _ _)))
  rcases unlockFinishTrace (f := f') (evm := lockSetPost evm true) v (by omega)
    (by simpa only [lockSetPost, transientStore_executionEnv] using hI)
    (by simpa only [lockSetPost, transientStore_σ₀] using hσ0)
    hp' hf hcaller hdata hresult hgas (by
      change C+(17+Ctload)+271+3*((len.toNat+31)/32)+Cₘ aw' ≤ C'+Cₘ aw at hcost
      norm_num [Ctload, GasConstants.Gwarmaccess] at hcost
      omega) hsize hrequest hsmall rdCall with hoog | ⟨result, hbody, hr⟩
  · exact .inl hoog
  · exact .inr ⟨result, execFuncBody_prepend hpref hbody, hr⟩

end Benchmarks.UniswapV4PoolManager
