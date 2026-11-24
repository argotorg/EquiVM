import Benchmarks.Auction.PauseRoutine
import Benchmarks.Auction.OwnershipRoutine

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem pauseBodySplit (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    (evm.executionEnv.perm = true → ExecTransitionBody fork auctionConfig auctionContract evm ∅ pauseTransition.body
      (.returned { contract := auctionContract, locals := ∅ }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
          (pauseWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))) none)) ∧
      (evm.executionEnv.perm = false →
        ExecTransitionBody fork auctionConfig auctionContract evm ∅
          pauseTransition.body .staticViolation) := by
  have hprefix {result : ExecResult}
      (htail : ExecBlock fork auctionConfig { contract := auctionContract, locals := ∅ } evm
        (pauseTransition.body.drop 2) result) :
      ExecBlock fork auctionConfig { contract := auctionContract, locals := ∅ } evm
        pauseTransition.body result :=
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalOwnerEq_true evm ∅ (by simp) ho)) htail)
  have hblock := pauseBlockSplit (fork := fork) evm ∅ (by simp) hp
  exact ⟨fun hperm ↦ ExecFuncBody.execBlockOK (hprefix (hblock.1 hperm)),
    fun hperm ↦ ExecFuncBody.execBlockStatic (hprefix (hblock.2 hperm))⟩

theorem pauseBody (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork auctionConfig auctionContract evm ∅ pauseTransition.body
      (.returned { contract := auctionContract, locals := ∅ }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
          (pauseWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))) none) :=
  (pauseBodySplit evm hwv ho hp).1 hperm

theorem pauseBodyAlreadyPaused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv)
    (hp : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecTransitionBody fork auctionConfig auctionContract evm ∅ pauseTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireStep
    (evalOwnerEq_true evm ∅ (by simp) ho)).run (pauseBlockReverts evm ∅ (by simp) hp)

theorem pauseBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 10))
    (hreach : EntryReached fork 10 σ σ₀ A I g) :
    runtimeRefinementFor fork auctionConfig auctionContract σ σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 10 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 10) (entryBytes_size 10) hsel
    have hdec : auctionConfig.externalABI.decodeCalldata?
        (pauseTransition.params.map Param.name)
        (transitionSignature pauseTransition).paramTypes I.calldata = some ∅ :=
      decodeCalldata_empty_ok hsz
    obtain ⟨_, _, rd685⟩ := hreach
    obtain ⟨_, _, rd698⟩ := entryGuardZero 10 (by decide) rd685 hwv
    have rd2080 := evm_run rd698 with [push2 ⟨413⟩, push2 ⟨2080⟩, jump (by jump_dest)]
    by_cases ho : solcSourceWord I = ownerWord σ I
    · obtain ⟨_, _, rd2122⟩ := ownerAllowed 4 rd2080 ho (by evm_ov)
      have rd3655 := evm_run rd2122 with [
        jumpdest, push2 ⟨1163⟩, push2 ⟨3655⟩, jump (by jump_dest) ]
      by_cases hp : pausedWord σ I = ⟨0⟩
      · rcases pauseRoutineOkSplit rd3655 hp (by jump_dest) (by evm_ov) with
          ⟨_hperm, _, _, rd1163⟩ | ⟨hperm, hstatic⟩
        swap
        · exact hstatic.reEquivStaticHalt hcode hd hdec
            ((pauseBodySplit
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) hwv ho hp).2 hperm)
        obtain ⟨_, _, rd413⟩ := auctionInternalReturn rd1163 (by jump_dest) (by evm_ov)
        have hbody := pauseBody (fork := fork) (hperm := _hperm)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) hwv ho hp
        exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGen
          hcode hd hdec hbody (by simp [storageStore_accountMap, initState,
            solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage])
          (.fallthrough rfl rfl (by native_decide))
      · have hbody := pauseBodyAlreadyPaused (fork := fork)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) hwv ho hp
        exact (pauseRoutineRevert rd3655 hp (by evm_ov)).reEquivExecutionRevert
          hcode hd hdec hbody
    · have hbody : ExecTransitionBody fork auctionConfig auctionContract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          pauseTransition.body .reverted := by
        apply ownerBodyReverts _ _ _ hwv
        · exact ho
        · simp
      exact (ownerDenied 4 rd2080 ho (by evm_ov)).reEquivExecutionRevert hcode hd hdec hbody
  · exact entryNonpayableRevert 10 (by decide) hcode hsel hreach hwv

end Auction
