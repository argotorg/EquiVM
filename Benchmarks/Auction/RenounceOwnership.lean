import Benchmarks.Auction.OwnershipRoutine
import Benchmarks.Auction.AddressSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem renounceOwnershipBody (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ renounceOwnershipTransition.body
      (.returned { contract := auctionContract, locals := ∅ }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) ⟨0⟩)) none) := by
  apply ExecFuncBody.execBlockOK
  exact nonpayableRequireAssignStorageBlock hwv (evalOwnerEq_true evm ∅ (by simp) ho)
    (evalZeroAddr _ _ _) (assignOwner evm ∅ ⟨0⟩ (by simp) (by decide))

theorem renounceOwnershipBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 8))
    (hreach : EntryReached 8 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 8 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 8) (entryBytes_size 8) hsel
    have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (renounceOwnershipTransition.params.map Param.name)
        (transitionSignature renounceOwnershipTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    obtain ⟨_, _, rd550⟩ := hreach
    obtain ⟨_, _, rd563⟩ := entryGuardZero 8 (by decide) rd550 hwv
    have rd2029 := evm_run rd563 with [push2 ⟨413⟩, push2 ⟨2029⟩, jump (by jump_dest)]
    by_cases ho : solcSourceWord I = ownerWord σ_evm I
    · obtain ⟨_, _, rd2071⟩ := ownerAllowed 3 rd2029 ho (by evm_ov)
      have rd3574 := evm_run rd2071 with [
        jumpdest, push2 ⟨1163⟩, push0, push2 ⟨3574⟩, jump (by jump_dest) ]
      obtain ⟨_, _, rd1163⟩ := transferOwnerRoutine rd3574 hperm (by jump_dest) (by evm_ov)
      obtain ⟨_, _, rd413⟩ := auctionInternalReturn rd1163 (by jump_dest) (by evm_ov)
      have hbody := renounceOwnershipBody
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hwv (by
          change solcSourceWord I = ownerWord σ_solm I
          rw [← ownerWord_equiv hAccounts I]
          exact ho)
      exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
        hcode hd hdec hbody (by rw [storageStore_createdAccounts]; rfl) (by
          rw [storageStore_accountMap]
          change accountMapEquiv
            (sstoreAccountMap I.codeOwner σ_evm ⟨151⟩
              (setAddressOffset0Word (storedWord σ_evm I ⟨151⟩) ⟨0⟩))
            (sstoreAccountMap I.codeOwner σ_solm ⟨151⟩
              (setAddressOffset0Word (storedWord σ_solm I ⟨151⟩) ⟨0⟩))
          rw [← storedWord_equiv hAccounts I ⟨151⟩]
          exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨151⟩ _ hAccounts)
        (.fallthrough rfl rfl (by native_decide))
    · have hbody : ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          renounceOwnershipTransition.body .reverted := by
        apply ownerBodyReverts _ _ _ hwv
        · change solcSourceWord I ≠ ownerWord σ_solm I
          rw [← ownerWord_equiv hAccounts I]
          exact ho
        · simp
      exact (ownerDenied 3 rd2029 ho (by evm_ov)).reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 8 (by decide) hcode hsel hreach hwv

end Auction
