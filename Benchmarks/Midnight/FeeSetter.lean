import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.Storage

variable {fork : Ethereum.Fork}

/-!
# Midnight `feeSetter()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9583; reach lemma `midnightReachFeeSetterBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem feeSetterBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork config contract evm ∅ feeSetterTransition.body
      (.returned (calldataFrame contract ∅ ∅ evm) evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩)
            solcAddrMask).toNat)])) := by
  exact guardedAddressGetter evm rfl rfl rfl (by decide) hwv hhi

/-- `feeSetter()`: the theorem `Correct.lean` routes selector 22 to. -/
theorem midnightFeeSetterBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 22)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 22) rfl hsel
  have hd : dispatchMsg contract I.calldata = some feeSetterTransition := by
    apply midnightDispatch_feeSetter <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  have hdec : config.externalABI.decodeCalldata? (feeSetterTransition.params.map Param.name)
      (transitionSignature feeSetterTransition).paramTypes I.calldata = some ∅ :=
    midnightDecodeEmpty hsz
  obtain ⟨k, C, rd⟩ := midnightReachFeeSetterBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  change RD fork _ _ _ _ _ _ midnightEntryMemory _ _ _ _ _ at rd
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_9583_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · have rd2 := midnightBlocks.midnight_block_9589_fallthrough (by simp)
        (by simpa only [midnightEntryMemory_zero] using
          entrySizeCheck_ok (bytes := 0) hsz hhi hsize) rd1
      have hr := midnightBlocks.midnight_block_9603 (by simp) rd2
      have hret : RDret fork midnightBytecode (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
          (UInt256.land (solcSlotWordAt ⟨10⟩ σ I) solcAddrMask).toByteArray := by
        change RDret fork _ _ _ _
          ((writeWord midnightEntryMemory (memLoad ⟨64⟩ midnightEntryMemory).toNat
            (UInt256.land (solcSlotWordAt ⟨10⟩ σ I) solcAddrMask)).readWithPadding
            (memLoad ⟨64⟩ midnightEntryMemory).toNat 32) at hr
        simpa only [midnightReturnWord_freePtr] using hr
      have hbody := feeSetterBodyReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I) hwv hhi
      exact hret.reEquivExecution hcode hd hdec hbody
        (returnEquiv_of_encode (solcAddressReturnEncoding rfl (solcSlotWordAt ⟨10⟩ σ I)))
    · have rd2 := midnightBlocks.midnight_block_9589_taken (by simp)
        (by
          have hc : UInt256.slt (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              ⟨0⟩ = ⟨1⟩ :=
            entrySizeCheck_huge (bytes := 0) (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [midnightEntryMemory_zero, hc]
          decide)
        (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivExecutionRevert hcode hd hdec (calldataSizeBodyReverts hwv hhi)
  · have rd1 := midnightBlocks.midnight_block_9583_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
