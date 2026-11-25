import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.PackedFields

variable {fork : Ethereum.Fork}

/-!
# Midnight `withdrawable(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9665; reach lemma `midnightReachWithdrawableBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawableBodyReturns (evm : EVM.State) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork config contract evm ((∅ : Store).insert "id" (wordBytes32Value key))
      withdrawableTransition.body
      (.returned (calldataFrame contract ((∅ : Store).insert "id" (wordBytes32Value key)) ∅ evm)
        evm (some [.int (Int.ofNat (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key + ⟨1⟩))
          (UInt256.ofNat (2^128 - 1))).toNat)])) := by
  apply guardedBytes32MappingFieldGetter (t := .int (.uint ⟨128, by decide⟩))
    (loc := {
      slot := solcMappingSlot ⟨1⟩ key + ⟨1⟩, offset := 0, size := 16,
      hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) evm key
    rfl rfl ?_ ?_ (by decide) (by decide) (by decide) hwv hhi
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))) + ⟨1⟩,
      offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)

theorem withdrawableTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 9683)
      [solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨1⟩) σ I)
        (UInt256.ofNat (2^128 - 1))).toByteArray := by
  have hr := midnightBlocks.midnight_block_9683 (by simp) rd
  simp only [midnightEntryMemory_zero] at hr
  simp only [uint128Mask_computed] at hr
  change RDret fork _ _ _ _
    ((writeWord (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)
      (memLoad (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)).toNat
      (UInt256.land (solcSlotWordAt (keccakWord
        (memLoad (UInt256.ofNat 800) (mappingMemory (calldataWord I.calldata 4) ⟨1⟩))
        (UInt256.ofNat 64)
        (mappingMemory (calldataWord I.calldata 4) ⟨1⟩) + ⟨1⟩) σ I)
        (UInt256.ofNat (2^128 - 1)))).readWithPadding
      (memLoad (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)).toNat 32) at hr
  rw [mappingMemory_zero, mappingMemory_hash, mappingMemory_freePtr] at hr
  exact (mappingMemory_return _ _ _) ▸ hr

/-- `withdrawable(bytes32)`: the theorem `Correct.lean` routes selector 20 to. -/
theorem midnightWithdrawableBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 20)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 20) rfl hsel
  have hd : dispatchMsg contract I.calldata = some withdrawableTransition := by
    apply midnightDispatch_withdrawable <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachWithdrawableBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_9665_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_9671_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hret := withdrawableTraceReturn rd2
        have hdec := midnightDecodeBytes32 "id" (by decide) (by decide) h36 hhi hsize
        have hbody := withdrawableBodyReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hwv hhi
        exact hret.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (uintReturnEncoding ⟨128, by decide⟩ _
            (u256LandMaskToNatLtOfToNat _ _ (by decide))))
      · have rd2 := midnightBlocks.midnight_block_9671_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "id" (.bytes abiBytes32Width)
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_9671_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "id" (.bytes abiBytes32Width)
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_9665_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (withdrawableTransition.params.map Param.name)
        (transitionSignature withdrawableTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)


end Benchmarks.Midnight
