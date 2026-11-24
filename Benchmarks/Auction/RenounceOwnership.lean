import Benchmarks.Auction.OwnershipRoutine
import Benchmarks.Auction.AddressSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem renounceOwnershipBodySplit (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv) :
    (evm.executionEnv.perm = true → ExecTransitionBody fork auctionConfig auctionContract evm ∅ renounceOwnershipTransition.body
      (.returned { contract := auctionContract, locals := ∅ }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
          (setAddressOffset0Word
            (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) ⟨0⟩)) none)) ∧
      (evm.executionEnv.perm = false →
        ExecTransitionBody fork auctionConfig auctionContract evm ∅
          renounceOwnershipTransition.body .staticViolation) := by
  have howner := evalOwnerEq_true evm ∅ (by simp) ho
  have hvalue := evalZeroAddr auctionConfig { contract := auctionContract, locals := ∅ } evm
  have hassign := assignOwner evm ∅ ⟨0⟩ (by simp) (by decide)
  constructor
  · intro hperm
    exact ExecFuncBody.execBlockOK
      (nonpayableRequireAssignStorageBlock hwv howner hvalue hassign hperm)
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (nonpayableRequireAssignStorageBlockStatic hwv howner hvalue hassign hperm)

theorem renounceOwnershipBody (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork auctionConfig auctionContract evm ∅ renounceOwnershipTransition.body
      (.returned { contract := auctionContract, locals := ∅ }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨151⟩
          (setAddressOffset0Word
            (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) ⟨0⟩)) none) :=
  (renounceOwnershipBodySplit evm hwv ho).1 hperm

theorem renounceOwnershipBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 8))
    (hreach : EntryReached fork 8 σ σ₀ A I g) :
    runtimeRefinementFor fork auctionConfig auctionContract σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 8 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 8) (entryBytes_size 8) hsel
    have hdec : auctionConfig.externalABI.decodeCalldata?
        (renounceOwnershipTransition.params.map Param.name)
        (transitionSignature renounceOwnershipTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    obtain ⟨_, _, rd550⟩ := hreach
    obtain ⟨_, _, rd563⟩ := entryGuardZero 8 (by decide) rd550 hwv
    have rd2029 := evm_run rd563 with [push2 ⟨413⟩, push2 ⟨2029⟩, jump (by jump_dest)]
    by_cases ho : solcSourceWord I = ownerWord σ I
    · obtain ⟨_, _, rd2071⟩ := ownerAllowed 3 rd2029 ho (by evm_ov)
      have rd3574 := evm_run rd2071 with [
        jumpdest, push2 ⟨1163⟩, push0, push2 ⟨3574⟩, jump (by jump_dest) ]
      rcases transferOwnerRoutineSplit rd3574 (by jump_dest) (by evm_ov) with
        ⟨_hperm, _, _, rd1163⟩ | ⟨hperm, hstatic⟩
      swap
      · exact hstatic.reEquivStaticHalt hcode hd hdec
          ((renounceOwnershipBodySplit
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) hwv ho).2 hperm)
      obtain ⟨_, _, rd413⟩ := auctionInternalReturn rd1163 (by jump_dest) (by evm_ov)
      have hbody := renounceOwnershipBody (fork := fork) (hperm := _hperm)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) hwv ho
      exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGen
        hcode hd hdec hbody (by
          rw [storageStore_accountMap]
          rfl)
        (.fallthrough rfl rfl (by native_decide))
    · have hbody : ExecTransitionBody fork auctionConfig auctionContract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          renounceOwnershipTransition.body .reverted := by
        apply ownerBodyReverts _ _ _ hwv
        · exact ho
        · simp
      exact (ownerDenied 3 rd2029 ho (by evm_ov)).reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 8 (by decide) hcode hsel hreach hwv

end Auction
